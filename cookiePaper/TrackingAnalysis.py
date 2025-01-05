# A library for analyzing tracking events.

import tldextract
from IPy import IP
import csv
import numpy as np
import functools
import time
import pymongo
import json
import collections
import operator
import pprint
import copy
import re
import datetime
from requests.cookies import RequestsCookieJar
import cookies
from http.cookiejar import Cookie
import http.cookies
from urllib.parse import urlparse
import urllib.request
from tabulate import tabulate
from cookies import Cookie as ThirdPartyCookie
from collections import defaultdict

import Utils

waybackRegex = re.compile('^https?://web.archive.org/web/\\d+[^/]*/(.*)')
waybackPathRegex = re.compile('^/web/(?P<archiveDate>\\d+)[^/]*/(?P<archivedUrl>.*)')
waybackTimeLimit = datetime.timedelta(days=182)

def setDD():
    return defaultdict(set)

class AnalysisEngine:
    '''Use a single Analysis Engine per run - there's no shared state between
    runs, so it makes sense to have a single instance of the engine per run.

            pass in events, one at a time or as an array
            at any time, can extract stats or go on

        The methods that already exist could be left as class methods or made
        into instance methods, not sure which makes more sense.
    '''

    def __init__(self, wayback, waybackTime=None, socialDomains=set(), 
                       csvfile=None, checkComputed=False, useCachedCookieDicts=False):
        self.wayback = wayback
        self.waybackTime = waybackTime
        if self.wayback != None and self.waybackTime != None:
            self.waybackTime = datetime.datetime.strptime(str(self.waybackTime), "%Y%m%d%H%M%S")
            self.pastLimit = self.waybackTime - waybackTimeLimit
            self.futureLimit = self.waybackTime + waybackTimeLimit
        self.TooFarPastOrFutureList = []
        self.cookieJar = RequestsCookieJar() 
        self.sitesToTrackersToTypes = defaultdict(setDD)
        self.trackersToSitesToTypes = defaultdict(setDD)
        self.processedEvents = []
        self.socialDomains = socialDomains
        self.rawEvents = []
        self.processedProgrammaticCookieSetEvents = []
        self.processedRequestEvents = []

        self.useCachedCookieDicts = useCachedCookieDicts

        self.siteToTabid = defaultdict(set)

        self.blockedEvents = 0

        self.numCookiesSet = 0
        self.numUniqueCookiesSet = 0
        self.cookiesDeleted = [] # might be unnecessary
        self.cookiesAdded = []

        self.checkComputedCookies = checkComputed

        self.typeDTrackers = []
        self.typeFTrackers = []
        
        self.cookieDirtyList = set()
        self.cachedCookieDicts = dict()

        self.errorCounts = collections.defaultdict(int)

        # Error tracking.
        self.tooFewDomains = []
        self.exceptionsInCheckSameCookies = 0
        self.eventsWithNullTopURL = 0
        self.eventsWithNullRequestURL = 0
        self.nonMatchingWithOneEmpty = 0
        self.nonMatchingComputedCookies = 0
        self.nonMatchingComputedCookiesDomains = []
        self.nonMatchingComputedCookiesTopDomains = []
        self.computedTooFew = 0
        self.computedTooMany = 0
        self.computedRightNumberStillWrong = 0
        self.matchingComputedCookies = 0
        self.programmaticCookieSetWithNullURLs = []
        self.invalidProgrammaticCookieSetStrings = []
        self.invalidSetCookieHeader = 0
        self.addToCookieStoreFailures = 0
        self.numCandidateCookieErrors = 0
        self.nonWaybackURLsFoundInRewriting = 0
        self.archiveOrgURLsFoundInRewriting = 0
        self.eventsWithNoCookiesInExtract = 0
        self.eventsWithSomeCookiesInExtract = 0
        self.noneCookiesInCandidates = 0
        
        self.eventProcessTimes = []

        if csvfile != None:
            self.cookieComparisonCSV = csv.writer(open(csvfile, 'w'))

        self.candidates = defaultdict(setDD)
        
    #########################################################
    ### Adding events and having them processed interface ###
    #########################################################
    def processEvents(self, events):
        '''Processes the given list of events.'''
        self.rawEvents.extend(events)
        for event in self._transformAll(events):
            start = time.time()
            self._processEvent(event)
            self.processedEvents.append(event)
            if event['type'] == 'programmaticCookieSet':
                self.processedProgrammaticCookieSetEvents.append(event)
            elif event['type'] == 'request':
                self.processedRequestEvents.append(event)
            end = time.time()
            self.eventProcessTimes.append(end - start)


    def _processEvent(self, event):
        if 'type' not in event:
            # raise ValueError('Processed event has no type.')
            # print('processed event has no type' + str(event))
            return False
        elif event['type'] == 'programmaticCookieSet':
            # 2 things happen for programmaticCookieSet events:
            #   1. We set the cookie in the cookie jar.
            #   2. We add the setter as an analytics candidate.
            if not event['top_url'] or not event['setting_script_url']:
                self.programmaticCookieSetWithNullURLs.append(event)
                return False
            topDomain = domainOf(event['top_url'])
            setterDomain = domainOf(event['setting_script_url'])
            if topDomain is None or setterDomain is None:
                return False
            self._extractEventCookiesToJar(event)

            try:    
                thirdPartyValue = ThirdPartyCookie.from_string(event['cookie_string']).value
                self.candidates[topDomain][setterDomain].add(thirdPartyValue)
            except Exception as e:
                self.numCandidateCookieErrors += 1
                # print(e)
                return None
        elif event['type'] == 'request':
            self._processRequestEvent(event)
        else:
            raise ValueError('Processed event has an invalid type: %s' % (event['type']))

    def _transformAll(self, events):
        '''This is a generator which iterates over the events given, transforming
        each of them if the engine is in wayback mode, returning a de-waybacked
        copy of each event in turn.'''
        for event in events:
            if self.wayback:
                event = self._transformWaybackEvent(event)
            if event != None:
                yield event

    def _transformWaybackEvent(self, event):
        if event['type'] == 'request':
            return self._transformRequestEvent(event)
        elif event['type'] == 'programmaticCookieSet':
            return self._transformCookieSetEvent(event)

    def _transformRequestEvent(self, event):
        '''Given a wayback request event, transform it to look like normal
        events that the event examining code will be happy with.
        This involves things like stripping normal headers, changing X-Archive-
        headers to normal ones, rewriting all the URLs to remove web.archive.org/web/,
        attaching Cookie: headers to the request as appropriate, etc. This must
        happen in flow with processing events, as it relies upon the current
        state of the cookie store.
        '''
        if not self.wayback:
            raise Exception('Transforming events while not in wayback mode.')
        
        newEvent = copy.deepcopy(event)

        # These are "toolbar" events, which should be invisible to the analysis
        # code since they wouldn't appear in the real web.
        if (not waybackRegex.match(event['request_url'])
            and domainOf(event['request_url']) == 'archive.org'):
                self.archiveOrgURLsFoundInRewriting += 1
                return None

        # Check the timestamps on request_url, referer_url, frame_url
        checkTimestampOn = [
            'request_url',
            'referer_url',
            'frame_url'
        ]
        for key in checkTimestampOn:
            if not self._checkTimestampInRange(event[key]):
                self.TooFarPastOrFutureList.append(event)
                return None
            
        # Rewrite URLs. 
        keysToRewrite = [ 
            'request_url',
            'top_url',
            'referer_url', 
            'frame_url'
        ]
        for key in keysToRewrite:
            newEvent[key] = self._unwaybackifyField(key, event)

            if newEvent[key] == NOT_A_WAYBACK_URL:
                newEvent[key] = event[key]

        # DON'T NEED?
        if newEvent.get('frame') != None and newEvent['frame'].get('url') != None:
            newEvent['frame']['url'] = getArchivedURLFromWaybackURL(newEvent['frame']['url'])
            if newEvent['frame']['url'] == NOT_A_WAYBACK_URL:
                newEvent['frame']['url'] = event['frame']['url']


        if newEvent.get('tab') != None and newEvent['tab'].get('url') != None:
            newEvent['tab']['url'] = getArchivedURLFromWaybackURL(newEvent['tab']['url'])
            if newEvent['tab']['url'] == NOT_A_WAYBACK_URL:
                newEvent['tab']['url'] = event['tab']['url']

        if newEvent.get('tab') != None and newEvent['tab'].get('faviconUrl') != None:
            newEvent['tab']['faviconUrl'] = getArchivedURLFromWaybackURL(newEvent['tab']['faviconUrl'])
            if newEvent['tab']['faviconUrl'] == NOT_A_WAYBACK_URL:
                newEvent['tab']['faviconUrl'] = event['tab']['faviconUrl']
        
        
        # Fix up the headers by removing non-X-Archive headers and stripping
        # X-Archive-Orig-.
        headers = newEvent.get('response_headers')
        if headers != None:
            # Remove all non X-Archive headers.
            headers = removeNonX_ArchiveHeadersFromHeaders(headers)
            
            # Remove X-Archive from all X-Archive-Orig- headers.
            # Leaves X-Archive-Playback-, X-Archive-Wayback-, 
            # X-Archive-Guessed- etc., unchanged.
            headers = stripX_Archive_OrigFromHeaders(headers)
        newEvent['response_headers'] = headers

        # Remove cookies from request headers
        headers = newEvent.get('request_headers')
        if headers != None:
            headers = [h for h in headers if not h.get('name', '') == 'Cookie']
        newEvent['request_headers'] = headers

        # Add cookies as appropriate.
        newEvent = self._addCookiesToEvent(newEvent)

        return newEvent

    def _transformCookieSetEvent(self, event):
        if not self.wayback:
            raise StandardError('Transforming events while not in wayback mode.')

        # Check the timestamps on request_url, referer_url, frame_url
        checkTimestampOn = [
            'top_url',
            'setting_script_url'
        ]
        for key in checkTimestampOn:
            if not self._checkTimestampInRange(event[key]):
                self.TooFarPastOrFutureList.append(event)
                return None
        
        newEvent = copy.deepcopy(event)
        newEvent['top_url'] = self._unwaybackifyField('top_url', event)
        newEvent['setting_script_url'] = self._unwaybackifyField('setting_script_url', event)
        return newEvent

    def _checkTimestampInRange(self, waybackURL):
        if not self.waybackTime:
            return True
        try:
            path = urlparse(waybackURL).path
            result = waybackPathRegex.match(path)
            timeInUrl = datetime.datetime.strptime(str(result.group('archiveDate')),"%Y%m%d%H%M%S")
            return timeInUrl > self.pastLimit and timeInUrl < self.futureLimit
        except Exception as e:
            return True
        return True

    def _unwaybackifyField(self, field, event):
        if field not in event:
            return None
        if event[field] == None:
            return None
        return getArchivedURLFromWaybackURL(event[field]) 

    def _noCookiesForDomain(self, domain):
        return len(self.cookieJar.get_dict(domain=domain)) == 0

    def _addCookiesToEvent(self, event):
        '''Given an event, add Cookie: headers to its request headers if appropriate,
        based on the current state of the cookie jar.'''

        if event['request_url'] == None:
            return event

        url = event['request_url']
        if not url.startswith('http'):
            url = 'http://%s' % (url,)

        req = urllib.request.Request(url=url)

        self.cookieJar.add_cookie_header(req)
        if requestObjectHasCookies(req):
            cookieStrings = getCookiesFromRequestObject(req)
            fullCookie = ';'.join(cookieStrings)
            if 'request_headers' not in event:
                event['request_headers'] = []
            event['request_headers'].append({
                'name': 'Cookie',
                'value': fullCookie
            })

        return event
            
    def _extractEventCookiesToJar(self, event):
        if 'type' not in event:
            raise KeyError('Event passed to _extractEventCookiesToJar has no type.')
        if event['type'] == 'programmaticCookieSet':
            url = event['top_url']
            if not url.startswith('http'):
                url = 'http://%s' % (url,)

            cookieStrings = [setCookieStringExpiresToInfinityOrZero(event['cookie_string'], event['timestamp'])]
            req = urllib.request.Request(url)
            resp = MockResponse(cookies=cookieStrings,
                                url=url)
            req = urllib.request.Request(url)

            self.cookieJar.extract_cookies(resp, req)
            self.cookieDirtyList.add(domainOf(url))

            # This is just for debugging
            ##########
            cookies = self.cookieJar.make_cookies(resp, req)
            if len(cookies) == 0:
                self.invalidProgrammaticCookieSetStrings.append(event['cookie_string'])
        elif event['type'] == 'request':
            url = event['request_url']
            if event['request_url'] == None:
                return
            if not url.startswith('http'):
                url = 'http://%s' % (url,)
            cookieStrings = getSetCookieFromEvent(event)
            if len(cookieStrings) == 0:
                self.eventsWithNoCookiesInExtract += 1
            else:
                self.eventsWithSomeCookiesInExtract += 1

            cookieStrings = [setCookieStringExpiresToInfinityOrZero(cs, event['request_time']) for cs in cookieStrings]

            req = urllib.request.Request(url)
            resp = MockResponse(cookies=cookieStrings,
                                url=url)
            self.cookieJar.extract_cookies(resp, req)
            self.cookieDirtyList.add(domainOf(url))

            # This is just for debugging
            ##########
            cookies = self.cookieJar.make_cookies(resp, req)
            if len(cookies) == 0 and len(cookieStrings) != 0:
                self.invalidSetCookieHeader += 1
        else:
            raise ValueError('Unrecognized type in event passed to _extractEventCookiesToJar')


    def _processRequestEvent(self, event):
        '''Processing a request has 2 (?) steps:
           1. Decide whether the request exhibits any tracking behaviors.
           2. Cookies. For any set-cookie headers, add the cookies to the store.
              This happens after deciding whether the request exhibits any tracking
              behaviors, since, cookies set in the response weren't present at the
              time of the request.
        '''
        tabid = tabIDForEvent(event)
        siteDomain = domainOf(event['top_url'])
        if tabid != None and siteDomain != None:
            self.siteToTabid[siteDomain + str(event['pass'])].add(tabid)

        if event['pass'] == 2:
            if self.checkComputedCookies:
                self.checkSameCookiesComputedAsOnRequest(event)

            if not event['top_url']:
                self.eventsWithNullTopURL += 1
                return
            elif not event['request_url']:
                self.eventsWithNullRequestURL += 1
                return
            # Is type A?
            retA = self.isTypeARequest(event)
            if retA is not None and 'site' in retA and 'tracker' in retA:
                self.sitesToTrackersToTypes[retA['site']][retA['tracker']].add('A')
                self.trackersToSitesToTypes[retA['tracker']][retA['site']].add('A')

            retD = self.isTypeDRequest(event)
            if retD is not None:
                self.sitesToTrackersToTypes[retD['site']][retD['leakedTo']].add('D')
                self.trackersToSitesToTypes[retD['leakedTo']][retD['site']].add('D')
                self.sitesToTrackersToTypes[retD['site']][retD['leakedTo']].add('D<')
                self.trackersToSitesToTypes[retD['leakedTo']][retD['site']].add('D<')
                self.sitesToTrackersToTypes[retD['site']][retD['leaker']].add('D>')
                self.trackersToSitesToTypes[retD['leaker']][retD['site']].add('D>')

                self.typeDTrackers.append(retD)
                
            # Is type F?
            retF = self.isTypeFRequest(event)
            for fTracker in retF:
                self.sitesToTrackersToTypes[fTracker['site']][fTracker['leakedTo']].add('F')
                self.trackersToSitesToTypes[fTracker['leakedTo']][fTracker['site']].add('F')
                self.sitesToTrackersToTypes[fTracker['site']][fTracker['leakedTo']].add('F<')
                self.trackersToSitesToTypes[fTracker['leakedTo']][fTracker['site']].add('F<')
                self.sitesToTrackersToTypes[fTracker['site']][fTracker['leaker']].add('F>')
                self.trackersToSitesToTypes[fTracker['leaker']][fTracker['site']].add('F>')

                self.typeFTrackers.append(retF)
                
            site = domainOf(event['top_url'])
            tracker = domainOf(event['request_url'])
            if site is not None and tracker is not None:
                # Is type B?
                if isTypeBRequest(event):
                    self.sitesToTrackersToTypes[site][tracker].add('B')
                    self.trackersToSitesToTypes[tracker][site].add('B')
                    #if 'gstatic.com' in event['request_url']:
                    #    print(getAllRequestCookieStringsFromEvent(event))
                # Is type B with cookie-triviality requirements applied?
                if isStrictTypeBRequest(event):
                    self.sitesToTrackersToTypes[site][tracker].add('strictB')
                    self.trackersToSitesToTypes[tracker][site].add('strictB')

                # Is third party request?
                if isThirdPartyRequest(event):
                    self.sitesToTrackersToTypes[site][tracker].add('3')
                    self.trackersToSitesToTypes[tracker][site].add('3')

                # Is type C?
                if isTypeCRequest(event):
                    self.sitesToTrackersToTypes[site][tracker].add('C')
                    self.trackersToSitesToTypes[tracker][site].add('C')

                # Is type E?
                if self.isTypeERequest(event):
                    self.sitesToTrackersToTypes[site][tracker].add('E')
                    self.trackersToSitesToTypes[tracker][site].add('E')

            # Other things we're counting?
            
        # Parse any set-cookies on the response, add to cookie store.
        self._extractEventCookiesToJar(event)


    ##########################################
    ### Getting results back out interface ###
    ##########################################
    #@functools.lru_cache(None)
    def getAllSites(self):
        return set([domainOf(s['top_url']) for s in self.processedEvents])
    
    def getAllSitesWithTrackers(self):
        return self.sitesToTrackersToTypes.keys()

    def getTrackersOnSite(self, site):
        return self.sitesToTrackersToTypes[site].keys()

    def getCombinedTypeOfTrackerOnSite(self, site, tracker):
        return ",".join(sorted(self.sitesToTrackersToTypes[site][tracker]))

    def getAllTrackers(self):
        return [k for k,v in self.trackersToSitesToTypes.items() if len(v) > 0]

    def getSitesWithTracker(self, tracker):
        return self.trackersToSitesToTypes[tracker].keys()

    def getNumSitesWithTracker(self, tracker):
        return len(self.trackersToSitesToTypes[tracker].keys())

    def getNumTrackersOfTypeOnSite(self, site, desiredType):
        if self.sitesToTrackersToTypes.get(site, None) == None:
            return 0
        count = 0
        for t, v in self.sitesToTrackersToTypes[site].items():
            if desiredType in v:
                count += 1
        return count

    # this function does not count trackers as B if they are also C or E
    def getTrackersOfTypeOnSite(self, site, desiredType):
        if self.sitesToTrackersToTypes.get(site, None) == None:
            return set()
        trackers = set()
        for t, v in self.sitesToTrackersToTypes[site].items():
            if desiredType in v:
                if desiredType == 'B':
                    if 'C' not in v and 'E' not in v:
                        trackers.add(t)
                else: # not a B
                    trackers.add(t)
        return trackers
                    
    def getNumSitesWithTrackersOfType(self, desiredType):
        siteCounts = defaultdict(int)
        for s in sitesToTrackersToTypes.keys():
            siteCounts[s] = 0
            for v in sitesToTrackerToTypes[site].values():
                if desiredType in v:
                    siteCounts[s] += 1
        return siteCounts
    
    def getAllTypesOfTracker(self, tracker):
        if tracker not in self.trackersToSitesToTypes:
            return set()
        if len(self.trackersToSitesToTypes[tracker]) == 0:
            return set()
        return set.union(*self.trackersToSitesToTypes[tracker].values())

    def getAllTrackersOfType(self, desiredType):
        trackers = self.getAllTrackers()
        trackersWithTypes = { t: self.getAllTypesOfTracker(t) for t in trackers }
        ofDesiredType = [t for t, types  in trackersWithTypes.items() if desiredType in types]
        return ofDesiredType

    def getAllTrackersOfMultipleTypes(self, typeFilter):
        if typeFilter == None:
            return set()
        ret = set()
        trackers = self.getAllTrackers()
        trackersWithTypes = { t: self.getAllTypesOfTracker(t) for t in trackers }
        for ty in typeFilter:
            ret = ret.union(set([t for t, types in trackersWithTypes.items() if ty in types]))
        return ret

    def getProcessedEventsCount(self):
        return len(self.processedEvents)

    def getCookiesSetCount(self):
        return self.numCookiesSet

    def getUniqueCookiesSetCount(self):
        return self.numUniqueCookiesSet

    def getProcessedEvents(self):
        return copy.deepcopy(self.processedEvents)

    def getWaybackEscapedRequests(self):
        pass

    def getAllTabIDs(self):
        return set([tabIDForEvent(e) for e in self.processedRequestEvents])
    
    def getTabIDsForSiteAndPass(self, domain, whichPass):
        return self.siteToTabid[domain + str(whichPass)]

    # Etc., etc.

    #####################################################
    # Classifications and helpers
    ####################################################

    def isTypeARequest(self, event):
        # Type A trackers occur in the following conditions:
        #  1. X loads a script _in the context of the page_
        #  2. X's script programmatically sets a cookie.
        #  3. A request is made to X's servers.
        #  4. The request includes the cookie value.

        # The platform requires that:
        #  a. The request is third party.
        #  b. The request is made to an analytics candidate's domain.
        #  c. That analytics candidate set a cookie on this domain.
        #  c. Some non-trivial cookie value the candidate set appears in the requestl URL.
        #  d. 

        #  ALSO: The request is not category D.

        # The platform's check just checks if (cookie_value in request_url).
        # This could miss POSTed parameters. We would miss them too, since
        # we don't have the body of POSTs.

        # a. Request is third party.
        if not isThirdPartyRequest(event):
            return None

        # b. Request is made to an analytics candidate for this domain.
        site = domainOf(event['top_url'])
        requestDomain = domainOf(event['request_url'])
        if site == None or site not in self.candidates:
            return None
        if requestDomain == None or requestDomain not in self.candidates[site]:
            return None

        # Grab the set of all cookies set on this domain by the candidate.
        candidateCookies = self.candidates[site][requestDomain]
        
        # c. Filter to non-trivial cookies.
        nonTrivialCookies = [c for c in candidateCookies if not isTrivial(c)]

        # d. Check whether any of them are in the URL.
        cookiesInRequest = [c for c in nonTrivialCookies if c in event['request_url']]

        if len(cookiesInRequest) > 0:
            return { 'site': site,
                     'tracker': requestDomain,
                     'cookiesLeaked': cookiesInRequest }

    def isTypeFRequest(self, event):
        # a. Request is third party.
        if not isThirdPartyRequest(event):
            return []

        topDomain = domainOf(event['top_url'])
        site = topDomain
        requestDomain = domainOf(event['request_url'])

        if topDomain is None or requestDomain is None:
            return []
        
        # b. Some cookies have been set by analytics candidates for this domain.
        if topDomain not in self.candidates:
            return []

        # c. Request is NOT made to an analytics candidate for this domain.
        for analyticsCandidate in self.candidates[topDomain]:
            if requestDomain == analyticsCandidate:
                return []

        trackers = []
        # A single request can implicate multiple candidates in type F tracking,
        # so we need to check all the candidates for the domain.
        for candidate, candidateCookies in self.candidates[topDomain].items():
            if candidateCookies is None:
                print(candidate + " had None cookies in self.candidates")
                return []
            # d. Filter to non-trivial cookies.
            nonTrivialCookies = [c for c in candidateCookies if not isTrivial(c)]

            # e. Check whether any of them are in the URL.
            cookiesInRequest = [c for c in nonTrivialCookies if c in event['request_url']]

            if (len(cookiesInRequest)) > 0:
                trackers.append({ 'site': site,
                                  'leaker': candidate,
                                  'leakedTo': requestDomain,
                                  'cookiesLeaked': set(cookiesInRequest) })

        return trackers

    def isTypeERequest(self, event):
        # A type E request is a type B or C request where the tracking domain
        # is also in a designated set of first-party "social" entities.
        # See platform commit 4a654586 at Background:783.
        if self.socialDomains is None:
            return False
        if not 'request_url' in event:
            return False
        pieces = tldextract.extract(event['request_url'])
        request_domain = '.'.join((pieces.domain, pieces.suffix))
        return ((isTypeBRequest(event) or isTypeCRequest(event)) and
                request_domain in self.socialDomains)

    ####################################

    def checkSameCookiesComputedAsOnRequest(self, event):
        '''This method is used in LIVE runs to verify that our cookie processing
        matches the ground truth contained in actual request events.'''
        try: 
            url = event['request_url']
            if not url.startswith('http'):
                url = 'http://%s' % (url,)
            req = urllib.request.Request(url=url)
            self.cookieJar.add_cookie_header(req)

            # computedCookies = ['cookie=value', 'cookie2=value2']
            computedCookies = getCookiesFromRequestObject(req)
            # browserCookies = ['cookie=value', 'cookie2=value2']
            browserCookies = getAllRequestCookieStringsFromEvent(event)

            # print('computed')
            # print(computedCookies)
            # print('browser')
            # print(browserCookies)


            if (computedCookies != browserCookies and 
               (len(computedCookies) == 0 or len(browserCookies) == 0)):
                self.nonMatchingWithOneEmpty += 1
               
            if computedCookies != browserCookies:
                # print('FAILURE')
                # # print(req.get_full_url())
                # print('computed: ' + str(computedParser))
                # print('browser: ' + str(browserParser))
                # print('cookies for domain %s: %s' % (domainOf(event['request_url']), str(self.cookieJar.get_dict(domain=domainOf(event['request_url'])))))
                # pprint.pprint(event)
                # print('-----')
                self.nonMatchingComputedCookies += 1
                self.nonMatchingComputedCookiesDomains.append(domainOf(event['request_url']))
                self.nonMatchingComputedCookiesTopDomains.append(domainOf(event['top_url']))
                if len(computedCookies) < len(browserCookies):
                    self.computedTooFew += 1
                    self.tooFewDomains.append(domainOf(event['request_url']))
                elif len(browserCookies) < len(computedCookies):
                    self.computedTooMany += 1
                else:
                    self.computedRightNumberStillWrong += 1

            else:
                self.matchingComputedCookies += 1
        except Exception as e:
            self.exceptionsInCheckSameCookies += 1
            pass


    def isTypeDRequest(self, event):
        # Leak own tracking cookies to 4th-party.
        # if not event['from_subframe']:
        #     return None

        if event['referer_url'] is None:
            return None

        refererDomain = domainOf(event['referer_url'])
        topDomain = domainOf(event['top_url'])
        requestDomain = domainOf(event['request_url'])
        if refererDomain == None or topDomain == None or requestDomain == None:
            return None
        if not isThirdPartyRequest(event) or not isThirdPartyToReferer(event):
            return None

        if self.useCachedCookieDicts:
            if refererDomain in self.cookieDirtyList:
                candidateCookieDict = self.cookieJar.get_dict(domain=refererDomain)
                self.cachedCookieDicts[refererDomain] = candidateCookieDict

                self.cookieDirtyList.discard(refererDomain)
                self.errorCounts['dirtyRecomputedCookieDicts'] += 1
            elif refererDomain in self.cachedCookieDicts:
                candidateCookieDict = self.cachedCookieDicts[refererDomain]
                self.errorCounts['cachedCookieDictsUsed'] += 1
            else:
                # This fallthrough never happens if we only check isTypeDRequest
                # on pass 2.
                candidateCookieDict = self.cookieJar.get_dict(domain=refererDomain)
                self.cachedCookieDicts[refererDomain] = candidateCookieDict
                self.cookieDirtyList.discard(refererDomain)
                self.errorCounts['uncachedRecomputedCookieDicts'] += 1
        else:
            candidateCookieDict = self.cookieJar.get_dict(domain=refererDomain)


        candidateCookies = candidateCookieDict.values()
        
        if candidateCookies == None:
            return None

        if None in candidateCookies:
            self.noneCookiesInCandidates += 1
            candidateCookies = [c for c in candidateCookies if c != None]
        
        # d. Filter to non-trivial cookies.
        nonTrivialCookies = [c for c in candidateCookies if not isTrivial(c)]

        # e. Check whether any of them are in the URL.
        cookiesInRequest = [c for c in nonTrivialCookies if c in event['request_url']]

        if len(cookiesInRequest) > 0:
            return {
                'leaker': refererDomain,
                'leakedTo': requestDomain,
                'site': topDomain,
                'event': event,
                'leakedCookies': cookiesInRequest,
            }
        else:
            return None

# End definition of AnalysisEngine class.
#####
# Begin module methods.


def isThirdPartyRequest(event):
    if 'request_url' not in event or event['request_url'] is None:
        return None
    if 'top_url' not in event or event ['top_url'] is None:
        return None

    requestDomain = tldextract.extract(event['request_url'])
    topDomain = tldextract.extract(event['top_url'])
    
    return (requestDomain.domain != topDomain.domain or 
            requestDomain.suffix != topDomain.suffix)

def isThirdPartyToReferer(event):
    if 'request_url' not in event or event['request_url'] is None:
        return None
    if 'referer_url' not in event or event ['referer_url'] is None:
        return None

    requestDomain = tldextract.extract(event['request_url'])
    refererDomain = tldextract.extract(event['referer_url'])

    return (requestDomain.domain != refererDomain.domain or 
            requestDomain.suffix != refererDomain.suffix)
    
def isStrictTypeBRequest(event):
    cookies = []
    for cs in getAllRequestCookieStringsFromEvent(event):
        try:
            cookie = ThirdPartyCookie.from_string(cs)
            cookies.append(cookie)
        except:
            pass
    cookieValues = [c.value for c in cookies]
    nonTrivialCookieValues = [cv for cv in cookieValues if not isTrivial(cv)]

    return (isThirdPartyRequest(event) and 
            len(nonTrivialCookieValues) > 0 and 
            event['window_type'] != 'popup')

def isTypeBRequest(event):
    # Type B requests have the following properties:
    #   Request has a cookie set. (Background.js:276)
    #   Request is 3rd party request. (Background.js:803,830,792)
    #   Is not a popup. (Background.js:810)
    return (hasCookies(event) and 
            isThirdPartyRequest(event) and
            event['window_type'] != 'popup')


NOT_A_WAYBACK_URL = '<[*NOT_A_WAYBACK_URL*]>'
def getArchivedURLFromWaybackURL(waybackURL):
    ''' Transform a given URL, which should be formatted like a wayback URL,
        into the URL that it archives. If it doesn't parse, this function returns
        a human readable constant NOT_A_WAYBACK_URL which indicates that the
        URL didn't seem to be a wayback URL. That constant contains characters
        which aren't allowed in URLs.
    '''
    if waybackURL is None:
        return None

    try: 
        query = urlparse(waybackURL).query
        path = urlparse(waybackURL).path
        path = (path if query == '' else '%s?%s' % (path, query))
        dp = tldextract.extract(waybackURL)
    except Exception as e:
        print('exception on ' + waybackURL)
        print(e)
        return NOT_A_WAYBACK_URL

    if '%s.%s.%s' % (dp.subdomain, dp.domain, dp.suffix) != 'web.archive.org':
        # print('Supposed wayback URL %s is not from web.archive.org!' % (waybackURL))
        return NOT_A_WAYBACK_URL

    result = waybackPathRegex.match(path)
    if result is None:
        # print(path)
        # print('Supposed wayback URL %s does not match our regex for a wayback URL!' % (waybackURL))
        return NOT_A_WAYBACK_URL

    return result.group('archivedUrl')

def findTypeBRequests(unorderedEvents):
    typeBTrackersBySite = {}
    for event in unorderedEvents:
        if isTypeBRequest(event):
            # print(event['top_url'])
            if (event['top_url'] not in typeBTrackersBySite) or (event['request_url'] not in typeBTrackersBySite[event['top_url']]):
                typeBTrackersBySite[event['top_url']] = event['request_url']

    return typeBTrackersBySite

def isTypeCRequest(event):
    '''Type C requests have the following properties:
       Request has a cookie set. (Background.js:276)
       Request is 3rd party request. (Background.js:803,792)
       Is a popup. (Background.js:810)

       We think there's a bug in the platform where it won't detect C if it has
       a referer. This code here doesn't have that bug.

       However, we can only detect upon initial opening of popup, because
       requests after that have nothing to compare the request_url to (they
       have no way of knowing what site opened the popup).
    '''
    return (hasCookies(event) and 
            isThirdPartyToReferer(event) and
            event['window_type'] == 'popup')

def hasCookies(event):
    if 'request_headers' not in event:
        return False
    return any([header['name'] == 'Cookie' for header in event['request_headers']])

def hasReferer(event):
    if 'request_headers' not in event:
        return False
    return any([header['name'] == 'Referer' for header in event['request_headers']])

@functools.lru_cache(maxsize=2**16)
def domainOfWB(url):
    return domainOf(getArchivedURLFromWaybackURL(url))

@functools.lru_cache(maxsize=2**16)
def domainOf(url):
    if url == None:
        return None
    pieces = tldextract.extract(url)
    if pieces.suffix == '':
        # check if it is an IP address
        try:
            ip = IP(pieces.domain)
            return pieces.domain
        except:
            #print('No suffix found and not an IP address by tldextract for %s domain: %s suffix: %s' % (url,pieces.domain, pieces.suffix,))
            return None
            #raise ValueError('No suffix found and not an IP address by tldextract for %s domain: %s suffix: %s' % (url,pieces.domain, pieces.suffix,))
    return '.'.join((pieces.domain, pieces.suffix))

def isTrivial(cookie):
    return (cookie == "www" or
            cookie == "true" or
            cookie == "false" or 
            cookie == "id" or
            cookie == "ID" or 
            cookie == "us" or
            cookie == "US" or
            cookie == "en_US" or
            cookie == "en_us" or
            cookie == "all" or
            cookie == "undefined" or
            len(cookie) <= 3)

def checkTrackerIsTypeOnSite(engine, tracker, tType, site):
    return tType in engine.sitesToTrackersToTypes.get(site, {}).get(tracker, set())

def combineAndSortEvents(requests, cookieSetEvents):
    # Combine them into a single list sorted by time.
    comboList0 = requests + cookieSetEvents

    # Filter out responses without matching requests.
    comboList = [event for event in comboList0 if 'timestamp' in event or 'request_time' in event]
    
    sortEvents = sorted(comboList, key=lambda e:(e['timestamp'] if 'timestamp' in e else e['request_time']))
    return sortEvents

def processEventsInEngine(engine, query, mongo):
    r =  mongo.hammer.run.find_one(query)
    run_name = r['run_name']
    requests = list(mongo.hammer.requestEvent.find({'run_name': run_name}))
    cookieSetEvents = list(mongo.hammer.programmaticCookieSetEvent.find({'run_name': run_name}))
    sortedEvents = combineAndSortEvents(requests, cookieSetEvents)
    engine.processEvents(sortedEvents)
    return engine.processedEvents
    
def getSortedEventsForRun(run_name, mongo):
    '''Input: Run name.
       Output: All events from that run, sorted by time.
    '''
    requestEvents = list(mongo.hammer.requestEvent.find({'run_name': run_name}))
    progSetEvents = list(mongo.hammer.programmaticCookieSetEvent.find({'run_name': run_name}))
    return combineAndSortEvents(requestEvents, progSetEvents)

def iterableRequestEventsForRun(run_name, host, port, fieldFilter=None):
    mongo = pymongo.MongoClient(host=host, port=port)
    if fieldFilter:
        cursor = mongo.hammer.requestEvent.find({'run_name': run_name}, fieldFilter)
    else: 
        cursor = mongo.hammer.requestEvent.find({'run_name': run_name})
    return cursor

@functools.lru_cache(maxsize=16)
def memoizedGetSortedEventsForRun(run_name, host, port):
    mongo = pymongo.MongoClient(host=host, port=port)
    return getSortedEventsForRun(run_name, mongo)

def filterTopURLsFromEventsList(events_list, toRemoveTopURLs):
    toRemove = set([domainOf(x) for x in toRemoveTopURLs])
    filteredEvents = [x for x in events_list if domainOf(x['top_url']) not in toRemove]
    # filteredEvents = [x for x in events_list if ('top_url' in x) and 
    #                                             (domainOf(x['top_url']) not in toRemove)]
                                                 
    return filteredEvents


def checkSameInputLists(mongo, run_name1, run_name2):
    run1 = mongo.hammer.run.find_one({'run_name': run_name1})
    run2 = mongo.hammer.run.find_one({'run_name': run_name2})
    if run1['input'] == run2['input']:
        print('Same input lists.')
    else:
        print('Input lists do not match.')
#        pprint(list(zip(liveRun['input'], waybackRun['input'])))
    
@functools.lru_cache(maxsize=16)
def memoizedFilterAndSort(run_name, host, port, toRemoveTopURLs):
    mongo = pymongo.MongoClient(host=host, port=port)
    return filterTopURLsFromRunAndSort(run_name, mongo, toRemoveTopURLs)

def filterTopURLsFromRunAndSort(run_name, mongo, toRemoveTopURLs):
    '''Input: Run name and list of URLs to remove
       Output: All events from that run, sorted by time except those with
               top_url in the toRemoveTopURLs list.
    '''
    progSetEvents = list(mongo.hammer.programmaticCookieSetEvent.find({'run_name': run_name}))
    progSetEvents = filterTopURLsFromEventsList(progSetEvents, toRemoveTopURLs)

    requestEvents = list(mongo.hammer.requestEvent.find({'run_name': run_name}))
    requestEvents = [e for e in requestEvents if 'top_url' in e]
    requestEvents = [e for e in requestEvents if e['top_url'] != None]
    requestEvents = filterTopURLsFromEventsList(requestEvents, toRemoveTopURLs)

    # print('After filter, %d request events, %d progSetEvents' % (len(requestEvents), len(progSetEvents)))
    
    return combineAndSortEvents(requestEvents, progSetEvents)

def stripX_Archive_OrigFromHeaders(headers):
    # Remove X-Archive from all X-Archive-Orig- headers.
    # Leaves X-Archive-Playback-, X-Archive-Wayback-, 
    # X-Archive-Guessed- etc., unchanged.
    
    strippedHeaders = []
    for header in headers:
        if 'name' not in header or 'value' not in header:
            strippedHeaders.append(header)
            continue
        archivedKey = header['name'].partition('X-Archive-Orig-')[2]
        if archivedKey != '':
            strippedHeaders.append({
                'name': archivedKey,
                'value': header['value']
            })
        else:
            strippedHeaders.append(header)

    return strippedHeaders

def removeNonX_ArchiveHeadersFromHeaders(headers):
    # By defaulting to an empty string, we implicitly drop all headers that don't
    # follow the name/value convention.
    onlyXArchiveHeaders = [h for h in headers if h.get('name', '').startswith('X-Archive-')]
    return onlyXArchiveHeaders

def requestObjectHasCookies(req):
    '''Given a urllib.request.Request object, check if it has a cookie header.'''
    return len([tup for tup in req.header_items() if tup[0].lower() == 'Cookie'.lower()]) == 1

def getCookiesFromRequestObject(req):
    if any([h[0].lower() == 'cookie'.lower() for h in req.header_items()]):
        cookieHeaders = [h[1] for h in req.header_items() if h[0].lower() == 'Cookie'.lower()]
        cookiesSeparated = [h.split(';') for h in cookieHeaders]
        cookieStrings = [item for sublist in cookiesSeparated for item in sublist]
        cookieStrings = [c.strip() for c in cookieStrings]
        cookieStrings.sort()
        return cookieStrings # ['foo=bar', 'baz=bon']
    else:
        return []

def getSetCookieFromEvent(event):
    if 'response_headers' not in event:
        return []
    if not event['response_headers']:
        return []
    return [header['value'] for header in event['response_headers'] if header['name'].lower() == 'set-cookie'.lower()]

def getAllRequestCookieStringsFromEvent(event):
    if 'request_headers' not in event:
        return []
    if not event['request_headers']:
        return []

    cookieHeaderValues = [header['value'] for header in event['request_headers'] if header['name'].lower() == 'cookie'.lower()]
    cookieHeaderValues = [h.split(';') for h in cookieHeaderValues]
    cookieStrings = [item for sublist in cookieHeaderValues for item in sublist]
    cookieStrings = [c.strip() for c in cookieStrings]
    cookieStrings.sort()
    return cookieStrings

def unix_time(dt):
    epoch = datetime.datetime.utcfromtimestamp(0)
    delta = dt - epoch
    return delta.total_seconds()

def unix_time_millis(dt):
    return unix_time(dt) * 1000.0

def createCookieFromString(cookieString, domain):
    try:
        c = ThirdPartyCookie.from_string(cookieString)
    except Exception as e:
        # print(e)
        return None
    return Cookie(
        version = c.version or 0,
        name = c.name,
        value = c.value,
        port = None,
        port_specified = False,
        domain = c.domain or domain,
        domain_specified = True, 
        domain_initial_dot = False,
        path = c.path or '/',
        path_specified = True,
        secure = c.secure or False,
        #expires = c.expires.strftime('%a, %d-%b-%Y %T GMT') if c.expires else None,
        # expires = c.expires or None,
        expires = unix_time(c.expires) if c.expires else None,
        # expires = 2000000000,
        # expires = 1,
        discard = False,
        comment = None,
        comment_url = None,
        rest = None
    )

def getEventAndResponseCount(run_name, mongo):
    numEvents = mongo.hammer.requestEvent.find({'run_name':run_name, 
                                                'request_time': {"$ne": None}}).count()
    yesResponse = mongo.hammer.requestEvent.find({'run_name':run_name, 
                                                  'request_time': {"$ne": None}, 
                                                  'response_time': {"$ne": None}}).count()
    return (numEvents, yesResponse)

def getResponseFraction(run_name, mongo):
    (numEvents, yesResponse) = getEventAndResponseCount(run_name, mongo)
    return yesResponse/numEvents

def getBlockedFraction(run_name, mongo):
    numEvents = mongo.hammer.requestEvent.find({'run_name':run_name}).count()
    blockedEvents = mongo.hammer.requestEvent.find({'run_name':run_name,
                                                    'blocked': True}).count()

    return blockedEvents/numEvents

def getHowManyRobotsBlocked(run_name, mongo):
    return mongo.hammer.requestEvent.count({'run_name': run_name, 'response_code': 403})

def getCompletedMainFrameCount(run_name, mongo):
    rQuery = {'run_name': run_name}
    completedItems = list(mongo.hammer.navigationCompletedEvent.find(rQuery))
    tabIdSet = set()
    completedQueries = []
    for i in completedItems:
        if i['tabId'] not in tabIdSet:
            completedQueries.append({'run_name': run_name, 'tab.id': i['tabId'],
                                     'request_url': i['url'], 'pass': i['pass'],
                                     'resource_type': 'main_frame'})
            tabIdSet.add(i['tabId'])
    mainFrameCount = 0
    for query in completedQueries:
        mainFrameCount += min(1, mongo.hammer.requestEvent.find(query).count())
    return mainFrameCount

def getRequestErrorCount(run_name, mongo):
    query = {'run_name': run_name, 'error_details': {'$exists': 1}}
    return mongo.hammer.requestEvent.find(query).count()

def getNavigationErrorCount(run_name, mongo):
    query = {'run_name': run_name}
    return mongo.hammer.navigationErrorEvent.find(query).count()

def getHowManyRequestsWithCookiesPass2(run_name, mongo):
    query = {'run_name': run_name, 'pass': 2, 'request_headers': {'$ne': None}}
    allReqs = mongo.hammer.requestEvent.find(query)
    result = 0
    for req in allReqs:
        for h in req['request_headers']:
            if h['name'] == 'Cookie':
                result += 1
                break
    return result

def getHowManyResponsesSetCookies(run_name, mongo):
    query = {'run_name': run_name, 'response_headers': {'$ne': None}}
    mode = mongo.hammer.run.find_one({'run_name': run_name})['mode']
    headNameToCheck = 'Set-Cookie'.lower()
    if mode == 'Wayback':
        headNameToCheck = 'X-Archive-Orig-Set-Cookie'.lower()
    allReqs = mongo.hammer.requestEvent.find(query)
    result = 0
    for req in allReqs:
        for h in req['response_headers']:
            if h['name'].lower() == headNameToCheck:
                result += 1
                break
    return result

def checkAllBlockedHaveNoResponse(run_name, mongo):
    impossibleEvents = mongo.hammer.requestEvent.find({'run_name': run_name,
                                                       'blocked': True,
                                                       'response_time': {'$ne': None}}).count()
    return impossibleEvents == 0   
                                    
# From https://iipc.github.io/openwayback/apidocs/org/archive/wayback/exception/WaybackException.html
# and https://iipc.github.io/openwayback/apidocs/org/archive/wayback/exception/AccessControlException.html 
ACCESS_CONTROL_EXCEPTIONS = [
    'AdministrativeAccessControlException', 
    'RobotAccessControlException', 
    'RobotNotAvailableException',
    'RobotTimedOutAccessControlException'
]
WAYBACK_EXCEPTIONS = [
    'AccessControlException',
    'AnchorWindowTooSmallException',
    'AuthenticationControlException',
    'BadQueryException',
    'BetterRequestException',
    'ConfigurationException',
    'LiveDocumentNotAvailableException',
    'LiveWebCacheUnavailableException',
    'LiveWebTimeoutException',
    'ResourceIndexNotAvailableException',
    'ResourceNotInArchiveException',
    'SpecificCaptureReplayException'
]

def requestHasArchiveRuntimeError(event):
    return getResponseHeader(event, 'X-Archive-Wayback-Runtime-Error')

def requestFailedDueToRobotAccessControlException(event):
    if event.get('type') == 'request':
        runtimeErrorHeaderValues = getResponseHeader(event, 'X-Archive-Wayback-Runtime-Error')
        if runtimeErrorHeaderValues is None:
            return False
        elif any([e.startswith('RobotAccessControlException') 
                  for e in runtimeErrorHeaderValues]):
            return True
        else:
            return False
        
    else:
        raise ValueError('Attempted to check if non-request event failed due to robots.txt')

def eventResourceWasNotArchived(event):
    if event.get('type') == 'request':
        runtimeErrorHeaderValues = getResponseHeader(event, 'X-Archive-Wayback-Runtime-Error')
        if runtimeErrorHeaderValues == None:
            return False
        elif any([e.startswith('ResourceNotInArchiveException') 
                  for e in runtimeErrorHeaderValues]):
            return True
        else:
            return False
        
    else:
        raise ValueError('Attempted to check if non-request event failed due to robots.txt')

def getResponseHeader(event, header):
    if 'response_headers' not in event:
        return []
    if not event['response_headers']:
        return []
    return [h['value'] for h in event['response_headers'] if h['name'].lower() == header.lower()]

def setCookieStringExpiresToInfinityOrZero(cookieString, bakedTimestamp):
    try:
        c = ThirdPartyCookie.from_string(cookieString)
        if c.expires == None:
            c.expires = datetime.datetime(2025, 1, 1, 0, 0, 0)
        elif isCookieExpired(c.expires, bakedTimestamp):
            c.expires = datetime.datetime(1970, 1, 1, 0, 0, 0)
        else:
            c.expires = datetime.datetime(2025, 1, 1, 0, 0, 0)
        return c.render_response()
    except:
        # We return empty string here because it won't result in a cookie.
        # Some of the things that cause exceptions are cookie strings like
        # '__test' (set by newstation.tv) which, if allowed to return unchanged,
        # result in cookies with value == None, which is problematic.
        return ''

def isCookieExpired(cookieExpireDatetime, bakedTimestamp):
    '''bakedTimestamp is the timestamp in ms after epoch at which the cookie was
    set . Cookie has a datetime on its cookie.expires property. Expired if 
    cookie.expires is in the past from the baked time.'''
    if cookieExpireDatetime == None:
        return False
    bakedDatetime = datetime.datetime.fromtimestamp(bakedTimestamp/1e3);
    return cookieExpireDatetime < bakedDatetime

def getMissingDomainsForRun(mongo, run_name):
    sites = mongo.hammer.run.find_one({'run_name': run_name})['sites_not_in_wayback']
    sites = [domainOf(s) for s in sites]
    return set(sites)
    
def findTrackersOnlyOnGivenDomains(engine, given):
    trackersOnGivenDomains = set()
    trackers = engine.getAllTrackers()
    for t in trackers:
        sites = list(engine.getSitesWithTracker(t))
        if len(sites) == 1 and sites[0] in given:
            # print('%s appears only on %s' % (t, sites[0]))
            trackersOnGivenDomains.add(t)

    return trackersOnGivenDomains

def requestsPerTabID(engine):
    counter = collections.Counter()
    
    for e in engine.processedEvents:
        if e['type'] != 'request':
            continue
        try:
            tabid = e['tab']['id']
            counter[tabid] += 1
        except:
            pass
    return counter

# Referer graph depth stuff
def getURLsBlockedByRobots(engine):
    '''This method takes an engine and returns 403'd URLs and the set of their
    domains in the engine.'''
    wb403Sites = set([e['request_url'] for e in engine.processedRequestEvents if e.get('response_code', 0) == 403])
    wb403Domains = set([domainOf(u) for u in wb403Sites])
    return wb403Sites, wb403Domains

# Single referer - exclude refering to self
def getSitesRefered(engine, referer):
    '''getSitesRefered takes an engine and a referer URL and returns the set of
    all URLs in the engine's events that have that referer. It finds everything
    in the engine referred to by the given referer.'''
    return set([e['request_url'] for e in engine.processedRequestEvents
                if 'referer_url' in e and e['referer_url'] == referer
                and e['request_url'] != referer])

# List of referers
def getSitesReferedByList(engine, listOfReferers):
    '''getSitesReferedByList takes an engine and a list of referers and returns
    all the request_urls from the engine that were referred by any of the referers
    in the list. It filters the request_urls of the engine down to only those
    which were referred by the given referers.'''
    hasReferer = [(e['referer_url'], e['request_url']) for e in engine.processedRequestEvents if 'referer_url' in e]
    hasRefererInList = set([reqUrl for (refUrl, reqUrl) in hasReferer if refUrl in listOfReferers])
    return hasRefererInList

def buildSubtreesDown(engine, setOfReferers, n):
    if n <= 0:
        return {}
    if len(setOfRequests) == 0:
        return {}    
    else: 
        return {refUrl: buildSubtreesDown(engine,
                                          getSitesRefered(engine, refUrl),
                                          n-1)
                for refUrl in setOfReferers}

# Should not refer to self
def getReferers(engine, request_url):
    '''Get the set of all referer_urls in the engine which ever refer to the given
    request URL and which aren't referring to themselves.'''
    return set([e['referer_url'] for e in engine.processedRequestEvents
                if 'referer_url' in e and e['request_url'] == request_url
                and e['referer_url'] != request_url])
    
def buildSubtreesUp(engine, setOfRequests, n):
    if n <= 0:
        return {}
    if len(setOfRequests) == 0:
        return {}
    else:
        return {reqUrl: buildSubtreesUp(engine,
                                        getReferers(engine, reqUrl),
                                        n-1)
                for refUrl in setOfRequests}

# Returns a nested pile of dicts 
def buildRefererGraphUp(engine, startingLeaves, maxdepth=10):
    return buildSubtreesUp(engine, set(startingLeaves), maxdepth)

# Returns a nested pile of dicts
def buildRefererGraphDown(engine, startingRoots, maxdepth=10):
    return buildSubtreesDown(engine, set(startingRoots), maxdepth)
    
# Returns a list of sets that are refered to at each depth
# refered[0] are refered to by the startingList
# refered[1] are refered to by refered[0] (but not startingList)
# refered[2] are refered to by refered[1] (but not startingList or refered[0])
# etc.
def calculateRefererGraphTopDown(engine, startingList, maxdepth=10):
    refered = []
    currRefererList = startingList
    previouslyReferers = startingList
    for i in range(maxdepth):
        refered.append(getSitesReferedByList(engine, currRefererList))
        if len(newBlocked) == 0:
            print("No new sites blocked at depth {}".format(i))
            break
        # else, continuing, so filter
        currRefererList = refered[i] - previouslyReferers
        previouslyReferers += currRefererList
    return refered

# Returns a list of sets that referer to the URLs of the previous depth
# If multiple URLs referer to a particular URL, all are included
def calculateRefererGraphBotUp(engine, startingList, maxHeight=10):
    referers = []

# Used for looking at Green/Red/Smilies

def getTrackersWithPrevalences(engine, typeFilter):
    allTrackersOfType = engine.getAllTrackersOfType(typeFilter)
    return { t: len(engine.trackersToSitesToTypes[t]) for t in allTrackersOfType }

def getCookieless(liveEngine, wbEngine):
    liveTrackers = getAllTrackersOfMultipleTypes('ABCDEF')
    cookies = collections.defaultdict(int)

    for c in wbEngine.cookieJar:
        domain = domainOf(c.domain)
        if domain in liveTrackers:
            cookies[domain] += 1
    noCookies = [domain for domain in liveTrackers if cookies[domain] == 0]
    return set(noCookies)

def getCookielessBs(liveEngine, wbEngine):
    liveTypeBs = set(liveEngine.getAllTrackersOfType('B'))
    cookies = collections.defaultdict(int)

    for c in wbEngine.cookieJar:
        domain = domainOf(c.domain)
        if domain in liveTypeBs:
            cookies[domain] += 1
    noCookies = [domain for domain in liveTypeBs if cookies[domain] == 0]
    return set(noCookies)

def getAllSmileys(liveEngine, wbEngine):
    liveTrackers = set(liveEngine.getAllTrackersOfMultipleTypes('ABCDEF'))
    wbTrackers = set(wbEngine.getAllTrackersOfMultipleTypes('ABCDEF'))

    return liveTrackers.intersection(wbTrackers)

def getSmileys(liveEngine, wbEngine):
    liveBs = set(liveEngine.getAllTrackersOfType('B'))
    wbBs = set(wbEngine.getAllTrackersOfType('B'))
    
    return liveBs.intersection(wbBs)

def getAllOnlyInWayback(liveEngine, wbEngine):
    liveTrackers = set(liveEngine.getAllTrackersOfMultipleTypes('ABCDEF'))
    wbTrackers = set(wbEngine.getAllTrackersOfMultipleTypes('ABCDEF'))

    return wbTrackers - liveTrackers

def getOnlyInWayback(liveEngine, wbEngine):
    liveBs = set(liveEngine.getAllTrackersOfType('B'))
    wbBs = set(wbEngine.getAllTrackersOfType('B'))
    
    return wbBs - liveBs

def getAllThirdsButNoCookies(liveEngine, wbEngine):
    cookieless = getCookieless(liveEngine, wbEngine)
    wbRequestURLs = [e['request_url'] for e in wbEngine.processedRequestEvents if isThirdPartyRequest(e)]
    wbHasRequestsDomains = set([domainOf(url) for url in wbRequestURLs])

    return wbHasRequestsDomains.intersection(cookieless)

def getThirdPartyRequestButNoCookies(liveEngine, wbEngine):
    cookielessBs = getCookielessBs(liveEngine, wbEngine)
    
    wbRequestURLs = [e['request_url'] for e in wbEngine.processedRequestEvents if isThirdPartyRequest(e)]
    wbHasRequestsDomains = set([domainOf(url) for url in wbRequestURLs])
    
    return wbHasRequestsDomains.intersection(cookielessBs)

def getAllRequestsButNoCookies(liveEngine, wbEngine):
    cookieless = getCookieless(liveEngine, wbEngine)
    wbRequestURLs = [e['request_url'] for e in wbEngine.processedRequestEvents]
    wbHasRequestsDomains = set([domainOf(url) for url in wbRequestURLs])

    return wbHasRequestsDomains.intersection(cookieless)

def getRequestButNoCookies(liveEngine, wbEngine):
    cookielessBs = getCookielessBs(liveEngine, wbEngine)
    
    wbRequestURLs = [e['request_url'] for e in wbEngine.processedRequestEvents]
    wbHasRequestsDomains = set([domainOf(url) for url in wbRequestURLs])
    
    return wbHasRequestsDomains.intersection(cookielessBs)

def getAllDomainsEverRobotsExclued(engine):
    return set([domainOf(e['request_url']) for e in engine.processedRequestEvents if requestFailedDueToRobotAccessControlException(e)])

def getNoEvidenceAllTrackers(liveEngine, wbEngine):
    liveTrackers = set(liveEngine.getAllTrackersOfMultipleTypes('ABCDEF'))
    wbRequestURLs = [e['request_url'] for e in wbEngine.processedRequestEvents]
    wbHasRequestsDomains = set([domainOf(url) for url in wbRequestURLs])

    return liveTrackers.difference(wbHasRequestsDomains)

def getNoEvidence(liveEngine, wbEngine):
    liveBs = set(liveEngine.getAllTrackersOfType('B'))
    
    wbRequestURLs = [e['request_url'] for e in wbEngine.processedRequestEvents]
    wbHasRequestsDomains = set([domainOf(url) for url in wbRequestURLs])
    
    return liveBs.difference(wbHasRequestsDomains)

def tabIDForEvent(event):
    if 'tab' in event and event['tab'] != None:
        return event['tab'].get('id')
    else:
        return None



def getEventsForTabID(engine, tabid):
    return [e for e in engine.processedRequestEvents if tabIDForEvent(e) == tabid]

def requests404sRatios(engine):
    '''Return dictionaries for the raw counts per domain, total requests per
    domain, and 404/request ratio per domain of the engine given.'''
    domainTo404sCount = collections.Counter()
    domainToRequestCount = collections.Counter()
    domainTo404sRatio = {}
    
    for event in engine.processedRequestEvents:
        domain = domainOf(event['request_url'])
        domainToRequestCount[domain] += 1
        if event.get('response_code', 0) == 404:
            domainTo404sCount[domain] += 1
    
    for domain in domainToRequestCount:
        domainTo404sRatio[domain] = 100 * domainTo404sCount[domain] / domainToRequestCount[domain]

    domainsWithAllRequests404s = set([domain for domain, ratio in domainTo404sRatio.items() if ratio == 100])
    # fully404sAndGreen = domainsWithAllRequests404s.intersection(greens)
    # any404s = set([domain for domain, ratio in domainTo404sRatio.items() if ratio > 0])
    # any404sAndGreen = any404s & greens
    
    # print('100%% 404s: %d' % len(domainsWithAllRequests404s))
    # print('>0 404s: %d' % len(any404s))
    # print('>0 404s and green: %d' % len(any404sAndGreen))
    # print('Fully 404s blocked AND green: %d' % len(fully404sAndGreen))

    # print('0%% 404s: %d (this should be > 0 since we are looking at all domains, not just those with some 404s blocks)' 
           # % len([domain for domain, ratio in domainTo404sRatio.items() if ratio == 0]))
    return domainTo404sCount, domainToRequestCount, domainTo404sRatio

def bubbleRequestsRatios(engine):
    domainToBubbleCount = collections.Counter()
    domainToRequestCount = collections.Counter()
    domainToBubbleRatio = dict()
    
    for event in engine.processedRequestEvents:
        domain = domainOf(event['request_url'])
        domainToRequestCount[domain] += 1
        if event['blocked']:
            domainToBubbleCount[domain] += 1
            
    for domain in domainToBubbleCount:
        domainToBubbleRatio[domain] = 100 * domainToBubbleCount[domain] / domainToRequestCount[domain]

    return domainToBubbleCount, domainToRequestCount, domainToBubbleRatio
    
def robotsRequestsRatios(engine):
    '''Return dictionaries for the raw counts of robots blocks per domain, total requests per
    domain, and robots/request ratio per domain of the engine given.'''
    domainToRobotsCount = collections.Counter()
    domainToRequestCount = collections.Counter()
    domainToRobotsRatio = {}
    
    for event in engine.processedRequestEvents:
        domain = domainOf(event['request_url'])
        domainToRequestCount[domain] += 1
        if requestFailedDueToRobotAccessControlException(event):
            domainToRobotsCount[domain] += 1
    
    for domain in domainToRequestCount:
        domainToRobotsRatio[domain] = 100 * domainToRobotsCount[domain] / domainToRequestCount[domain]
        
    return domainToRobotsCount, domainToRequestCount, domainToRobotsRatio

def inconsistentTimestampRatio(engine):
    '''Return dictionaries for the raw counts of inconsistent timestamps per domain, total requests per domain, and inconsistent/request ratio per domain of the engine given.'''
    domainToInconsistentCount = collections.Counter()
    _, domainToRequestCount, _ = bubbleRequestsRatios(engine) #easiest way to get requests total, since it comes from a different list
    domainToInconsistentRatio = {}
   
    for event in engine.TooFarPastOrFutureList:
        if event['type'] == 'request':
            domain = domainOf(engine._unwaybackifyField(event['request_url']))
            domainToInconsistentCount[domain] += 1
    
    for domain in domainToRequestCount:
        domainToInconsistentRatio[domain] = 100 * domainToInconsistentCount[domain] / domainToRequestCount[domain]
        
    return domainToInconsistentCount, domainToRequestCount, domainToInconsistentRatio

def getSiteTrackerCounts(engine, typeFilter):
    siteTrackerCounts = collections.Counter()
    for site in engine.getAllSites():
        trackers = engine.sitesToTrackersToTypes[site]
        if len(trackers) == 0:
            siteTrackerCounts[site] = 0
        else:
            for tracker, types in trackers.items():
                if set(typeFilter) & types:
                    siteTrackerCounts[site] += 1

    return siteTrackerCounts

def averageTrackersPerSite(engine, typeFilter):
    siteTrackerCounts = getSiteTrackerCounts(engine, typeFilter)
    return np.mean(list(siteTrackerCounts.values()))

def getMostTrackedSites(engine, typeFilter, N):
    siteTrackerCounts = getSiteTrackerCounts(engine, typeFilter)
    return siteTrackerCounts.most_common(N)
    

def getInstancesOfType(engine, typeFilter):
    instances = 0
    trackersOfType = engine.getAllTrackersOfType(typeFilter)
    for tracker in trackersOfType:
        sites = engine.trackersToSitesToTypes[tracker]
        for types in sites.values():
            if typeFilter in types:
                instances += 1

    return instances

def getSocialDomains(year):
    with open('socialTrackerLists/%ssocialTrackers.txt' % year, 'r') as f:
        socials = f.readlines()
        socials = [d.strip() for d in socials]
        return set(socials)

def getLiveRun(mongohost, mongoport, year, liveRunName, comparableWaybackRunName):
    import pymongo
    mongo = pymongo.MongoClient(host=mongohost, port=mongoport)
    missingFromArchive = mongo.hammer.run.find_one({'run_name': comparableWaybackRunName})['sites_not_in_wayback']
    socialDomains = getSocialDomains(year)
    liveEngine = AnalysisEngine(wayback=False, socialDomains=socialDomains)
    events = memoizedFilterAndSort(liveRunName, mongohost, mongoport, tuple(missingFromArchive))
    liveEngine.processEvents(events)
    liveEngine.run_name = liveRunName
    return liveEngine

@Utils.timefunc
def analyzeWholeWaybackRun(run, waybackTime, port=9999, checkComputed=False, socialDomains=set()):
    engine = AnalysisEngine(wayback=True, waybackTime=waybackTime, checkComputed=checkComputed, socialDomains=socialDomains)
    events = memoizedGetSortedEventsForRun(run, 'localhost', port)
    engine.processEvents(events)
    engine.run_name = run
    return engine

def sortedEngines(engines, firstYear=None): 
    if firstYear:
        return [e[1] for e in sorted(engines.items()) if e[0] >= firstYear]
    else:
        return [e[1] for e in sorted(engines.items())]
def sortedEngineYears(engines, firstYear=None):
    if firstYear:
        return [e[0] for e in sorted(engines.items()) if e[0] >= firstYear]
    else:
        return [e[0] for e in sorted(engines.items())]

def getArchiveTime(url):
    path = urlparse(url).path
    result = waybackPathRegex.match(path)
    if result:
        return result.group('archiveDate')

    raise ValueError('%s is not a wayback URL' % url)
    

def isAnachronism(event, pastLimit, futureLimit):
    # need to check 'top_url', 'frame'.'url', 'setting_script_url'
    checkList = [event[u] for u in ['top_url', 'setting_script_url']]
    if 'frame' in event and 'url' in event['frame']:
        checkList.append(event['frame']['url'])
        #print(checkList)
    for u in checkList:
        try:
            path = urlparse(u).path
            result = waybackPathRegex.match(path)
            if result:
                timeInUrl = datetime.datetime.strptime(str(result.group('archiveDate')),"%Y%m%d%H%M%S")
                if timeInUrl < pastLimit or timeInUrl > futureLimit:
                    return True
        except Exception as e:
            continue
            #print("Exception in isAnachronism({}, {}, {}): {}".format(event, pastLimit, futureLimit, e))
    return False


class MockResponse():
    '''Looks enough like a urllib.response for cookie jars to allow it to be used
    in a call to jar.make_cookies(resp, req)'''
    def __init__(self, cookies, url):
        '''Cookies should be a list of Set-Cookie header _values_.'''
        self.headers = MockHeaders(cookies)
        self.url = url

    def info(self):
        return self.headers

class MockHeaders():
    '''Looks enough like an email.message.Message for cookie jars to allow it 
    to be used as the turn value of resp.info() in a call to jar.make_cookies(resp, req)'''
    def __init__(self, cookies):
        self.cookies = cookies

    def get_all(self, header, default):
        if header.lower() == 'Set-Cookie'.lower():
            return self.cookies
        else:
            return default
