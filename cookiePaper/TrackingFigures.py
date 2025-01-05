# A library for making figures about analyzed tracking.

import math
import numpy
import pprint
import csv
import re
import datetime
from collections import defaultdict, Counter
from tabulate import tabulate
import matplotlib
import matplotlib.pyplot as plt
import pandas as pd
import seaborn as sns
import TrackingAnalysis as TA
from tabulate import tabulate
from collections import defaultdict, Counter
from pymongo import ReturnDocument

xtickSize = 14
ytickSize = 14
ylabelSize = 18
xlabelSize = 18
titleSize = 22
legendSize = 14

def deleteRun(mongo, run_name):
  mongo.hammer.run.remove({'run_name': run_name})
  mongo.hammer.requestEvent.remove({'run_name': run_name})
  mongo.hammer.programmaticCookieSetEvent.remove({'run_name': run_name})
  mongo.hammer.navigationCompleteEvent.remove({'run_name': run_name})
  mongo.hammer.navigationErrorEvent.remove({'run_name': run_name})

def timeStringToDatetime(timeString):
  dl = re.split('\W+|/|:|,', timeString)
  
  dl[0] = dl[0].zfill(2)
  dl[1] = dl[1].zfill(2)
  dl[3] = dl[3].zfill(2)
  cleanedString = "".join(dl)
  return datetime.datetime.strptime(cleanedString, "%m%d%Y%I%M%S%p")

#####
# CSV Utilities
####

def saveCSV(table, filename):
  with open(filename, 'w') as csvfile:
    writer = csv.writer(csvfile, delimiter=',')
    writer.writerows(table)
    
def loadCSV(filename):
  with open(filename, 'r') as csvfile:
    reader = csv.reader(csvfile, delimiter=',')
    responseTable = []
    for row in reader:
      responseTable.append(row)
  return responseTable

def csvToPandas(filename, index=False):
  df = pd.read_csv(filename, index_col=index)
  return df

def resortRunsByRunName(df):
  df['sortColumn'] = df.apply(lambda row: (timeStringToDatetime(row['run_name'][4:]) - datetime.datetime(1970,1,1)).total_seconds(), axis=1)
  #print(df[['run_name', 'sortColumn']])
  df = df.sort(columns='sortColumn')
  df = df.drop('sortColumn', 1)
  #print(df[['run_name']])
  print(df.tail())
  return df

def isInRunNameList(i):
  runNameList = [r['run_name'] for r in mongo.hammer.run.find({'end_time': {'$ne': None}})]
  return i in runNameList

def removeDeletedRunsFromCSV():
  df = pd.read_csv('allRunsInfo.csv')
  df = df[df.run_name.map(isInRunNameList) == True]
  writeAndCheck(df, 'allRunsInfo.csv')
  df = pd.read_csv('waybackRunsInfo.csv')
  df = df[df.run_name.map(isInRunNameList) == True]
  writeAndCheck(df,'wabyackRunsInfo.csv')

def countRequestStarts(run_name):
  r = mongo.hammer.run.find_one({'run_name': run_name})['platform_event_counts']
  return r['pass1']['request_starts'] + r['pass2']['request_starts']

def countProgrammaticSets(run_name):
  r = mongo.hammer.run.find_one({'run_name': run_name})['platform_event_counts']
  return r['pass1']['cookie_sets'] + r['pass2']['cookie_sets']

def writeAndCheck(df, filename):
  df.to_csv(filename, index=False)
  df = pd.read_csv(filename)
  print(df.head())

def updateMongoFromCSV(mongo):
  allRuns = csvToPandas('allRunsInfo.csv', 'run_name')
  waybackRuns = csvToPandas('waybackRunsInfo.csv', 'run_name')

  runNames =[run['run_name'] for run in mongo.hammer.run.find({'response_fraction': {'$exists': False}})]
  #[mongo.hammer.run.find_one({'response_fraction': {'$exists': True}})['run_name']]
  #runNames = [run['run_name'] for run in mongo.hammer.run.find({'response_fraction': {'$exists': True}, 'archived_fraction': {'$exists': False}})] 

  print("{} update candidates".format(len(runNames)))
  
  modifiedCount = 0
  waybackModifiedCount = 0
  keyErrors = 0
  for rname in runNames:
    #print(rname)
    try:
      allRunsRow = allRuns.loc[rname]
    except KeyError:
      keyErrors += 1
      continue;

    response_sets_cookie = 0
    #print(type(allRunsRow['response_sets_cookie']))
    if not math.isnan(allRunsRow['response_sets_cookie']):
      response_sets_cookie = int( allRunsRow['response_sets_cookie'])
    update = {'$set': {'response_fraction': float(allRunsRow['response_fraction']),
                       '400_errors': int(allRunsRow['400_errors']),
                       'request_errors': int(allRunsRow['request_errors']),
                       'p2_requests_with_cookies': int(allRunsRow['requests_with_cookies_p2']),
                       'response_sets_cookie': response_sets_cookie
                     }}
    mongo.hammer.run.update_one({'run_name': rname}, update)
    modifiedCount += 1

    if allRunsRow['mode'] == "Wayback":
      wbRunsRow = waybackRuns.loc[rname]
      update = {'$set': {'archived_fraction': float(wbRunsRow['archived_fraction']),
                         'blocked': int(wbRunsRow['blocked']),
                         'robots_blocked': int(wbRunsRow['robots_blocked'])
                       }}
      mongo.hammer.run.update_one({'run_name': rname}, update)
      waybackModifiedCount += 1
  print("{} updated and {} wayback, {} key errors".format(modifiedCount, waybackModifiedCount, keyErrors))
                       
# Tracker Type || Unique Trackers of Type | Instances of these trackers (min occurance, max occurance)
def table3(mongo, query, wayback=False, printResults=True, socialDomains=set()):
  engine = TA.AnalysisEngine(wayback, socialDomains=socialDomains)
  query['end_time'] = {'$ne': None}
  r =  mongo.hammer.run.find_one(query)
  run_name = r['run_name']
  requests = list(mongo.hammer.requestEvent.find({'run_name': run_name}))
  cookieSetEvents = list(mongo.hammer.programmaticCookieSetEvent.find({'run_name': run_name}))
  sortedEvents = TA.combineAndSortEvents(requests, cookieSetEvents)
  engine.processEvents(sortedEvents)
  
  combinedTypeCounts = defaultdict(list)
  for s in engine.getAllSitesWithTrackers():
    for t in engine.getTrackersOnSite(s):
      ctype = engine.getCombinedTypeOfTrackerOnSite(s, t)
      combinedTypeCounts[engine.getCombinedTypeOfTrackerOnSite(s, t)].append(t)

  table = []
  for (ctype, trackerList) in combinedTypeCounts.items():
    c = Counter(trackerList)
    temp = c.most_common()
    table.append([ctype, 
                  len(set(trackerList)), 
                  len(trackerList), 
                  str(temp[-1][0]) + ',' + str(temp[-1][1]), 
                  str(temp[0][0]) + ',' + str(temp[0][1])])
  table.sort()
  if printResults:
    print("Statistics for run for " + run_name + " " + str(query))
    print(tabulate(table, headers=["Tracker Type", "# Unique Trackers",
                                   "# Instances", "Min", "Max"]))
    print("\n")
  return table, engine

def table3WithSocial(mongo, query, socialFilename, wayback=False, printResults=True):
  socialSet = set()
  with open(socialFilename, 'r') as socialF:
    for line in socialF:
      socialSet.add(line.strip())
      

  print('Social set open with length {}'.format(len(socialSet)))
  table3(mongo, query, wayback, printResults, socialSet)

def table3WithEngine(engine, printResults=True):
  combinedTypeCounts = defaultdict(list)
  for s in engine.getAllSitesWithTrackers():
    for t in engine.getTrackersOnSite(s):
      ctype = engine.getCombinedTypeOfTrackerOnSite(s, t)
      combinedTypeCounts[engine.getCombinedTypeOfTrackerOnSite(s, t)].append(t)

  table = []
  for (ctype, trackerList) in combinedTypeCounts.items():
    c = Counter(trackerList)
    temp = c.most_common()
    table.append([ctype, 
                  len(set(trackerList)), 
                  len(trackerList), 
                  str(temp[-1][0]) + ',' + str(temp[-1][1]), 
                  str(temp[0][0]) + ',' + str(temp[0][1])])
  table.sort()
  if printResults:
    print(tabulate(table, headers=["Tracker Type", "# Unique Trackers",
                                   "# Instances", "Min", "Max"]))
    print("\n")
  return table
  
def checkIfRowInTable(run_name, table):
  for row in table:
    if run_name == row[0]:
      return True
  return False

def delFirstColumnIfNeeded(table):
  table.sort()
  for row in table:
    if row[0] != 'run_name':
      del row[0]

# All run stats to CSV
def writeAllRunsCSV(mongo, inTable=None):
  table = []
  i = 0
  if inTable == None:
    inTable = [['run_name', 'mode', 'input_length', 'parallelism',
                'time_on_page', 'run_time', 'response_fraction', '400_errors',
                'main_frame_nav_complete', 'nav_errors', 'request_errors',
                'total_request_starts', 'programmatic_sets',
                'requests_with_cookies_p2', 'response_sets_cookie']]
  for r in mongo.hammer.run.find({'end_time': {'$ne': None}}):
    if checkIfRowInTable(r['run_name'], inTable):
      continue

    if i == 0:
      print("about to append first item: " + r['run_name'])
                
    rname = r['run_name']
    totalRequests, withResponse = TA.getEventAndResponseCount(rname, mongo)
    frac = withResponse/totalRequests
    #frac = "Not measured"
    startTime = timeStringToDatetime(r['start_time'])
    endTime = timeStringToDatetime(r['end_time'])
    runTime = endTime - startTime

    http400Errors = mongo.hammer.requestEvent.find(
      {'run_name': rname, 'response_code': 400,
       'request_time': {'$exists': True}} ).count()
    #http400Errors = "Not measured"

    main_nav_complete = TA.getCompletedMainFrameCount(rname, mongo)
    if r['mode'] != "Wayback":
       main_nav_complete /= (2*r['input_length'])
    else:
      main_nav_complete /= (2*len(r['wayback_urls_of_input']))
    nav_errors = TA.getNavigationErrorCount(rname, mongo)
    request_errors = TA.getRequestErrorCount(rname, mongo)


    progSets = r['platform_event_counts']['pass1']['cookie_sets'] + r['platform_event_counts']['pass2']['cookie_sets']

    if r['mode'] == 'Normal': 
      reqsWithCookies = TA.getHowManyRequestsWithCookiesPass2(rname, mongo)
    else:
      reqsWithCookies = "NA"
    settingCookies = TA.getHowManyResponsesSetCookies(rname, mongo)
    
    
    table.append([timeStringToDatetime(rname[4:]), rname, r['mode'],
                  r['input_length'], r['parallelism'], 
                  r['seconds_to_remain_on_page'], runTime, 
                  frac, http400Errors, main_nav_complete,
                  nav_errors, request_errors,
                  totalRequests, reqsWithCookies, settingCookies])
    print('Append ' + str(i) +" " + rname)
    i += 1
    if i == 1:
      break

  delFirstColumnIfNeeded(table)
  outTable = inTable + table
  saveCSV(outTable, "allRunsInfo.csv")

def waybackStatsToCSV(mongo, inTable=None):
  table = []
  i = 0
  if inTable == None or inTable == False or inTable == "False":
    inTable = [['run_name', 'wayback_time', 'input_length', 'parallelism',
                'time_on_page', 'run_time', 'archived_fraction',
                'main_frame_nav_complete', 'nav_errors', 'blocked',
                'response_fraction', '400_errors',  'request_errors',
                'robots_blocked']]
  for r in mongo.hammer.run.find({'mode': 'Wayback', 'end_time': {'$ne': None}}, batch_size=30): 
    if checkIfRowInTable(r['run_name'], inTable):
      continue
    rname = r['run_name']
    print("Will append " + rname)

    startTime = timeStringToDatetime(r['start_time'])
    endTime = timeStringToDatetime(r['end_time'])
    runTime = endTime - startTime
    
    waybackCount = len(r['wayback_urls_of_input'])
    if (waybackCount != (r['input_length'] - len(r['sites_not_in_wayback']))):
      print("Unequal lengths. Input: %d wayback urls: %d not in wayback: %d" 
            % (r['input_length'], len(r['wayback_urls_of_input']), len(r['sites_not_in_wayback']),))
    
    waybackFraction = waybackCount/r['input_length']
        
    numEvents,yesEvents = TA.getEventAndResponseCount(rname, mongo)
    frac = str(yesEvents)+" / "+str(numEvents)+" = {:.0%}".format(yesEvents/numEvents)
    #frac = "Not measured"
        
    blockedEvents = mongo.hammer.requestEvent.find({'run_name': rname, 'blocked': True}).count()
    #blockedFraction = blockedEvents/numEvents
    robotsBlocked = TA.getHowManyRobotsBlocked(rname, mongo)
        
    http400Errors = mongo.hammer.requestEvent.find({'run_name': rname, 'response_code': 400, 'request_time': {'$exists': True}}).count()
    main_nav_complete = TA.getCompletedMainFrameCount(rname, mongo) / (2*waybackCount)
    nav_errors = TA.getNavigationErrorCount(rname, mongo)
    request_errors = TA.getRequestErrorCount(rname, mongo)
    
    table.append([timeStringToDatetime(rname[4:]), rname, r['wayback_time'],
                  r['input_length'], r['parallelism'],
                  r['seconds_to_remain_on_page'], 
                  runTime, waybackFraction, main_nav_complete,
                  nav_errors, blockedEvents,
                  frac, http400Errors, request_errors, robotsBlocked])
    print('Append ' + str(i) +" " + rname)
    i += 1
    if i == 1:
      break
  delFirstColumnIfNeeded(table)
  outTable = inTable + table
  saveCSV(outTable, "waybackRunsInfo.csv")

def analyzeNewRuns(mongo, fromFile=True):
  initTable = None
  print("Analysis called with loadFromFile: " + str(fromFile))
  if fromFile == True:
    initTable = loadCSV("allRunsInfo.csv")
    print("allRunsInfo.csv loaded")
  print("Starting analysis of all runs...")
  writeAllRunsCSV(mongo, initTable)

  if fromFile == True:
    initTable = loadCSV("waybackRunsInfo.csv")
  print("Starting analysis of wayback runs...")
  waybackStatsToCSV(mongo, None)

  print("Analysis complete")

def describeRun(mongo, run_name):
  run = mongo.hammer.run.find_one({'run_name': run_name})
  print('Run %s (mode: %s) found in DB with input_length %d' %
        (run['run_name'], run['mode'], run['input_length']))

# engine is the one used for calculating the referer graph.
# secondEngine is just used for seeing whether the trackers in engine show up in a second run
# for example, engine=live and secondEngine=wayback, can see which live trackers were visible/trackers in wayback
def infoAboutReferersFromTopDown(engine, startingList, secondEngine=None, maxDepth=10):
  print("Starting list len {}".format(len(set(startingList))))
  refered = calculatedRefererGraphTopDown(engine, startingList, maxDepth)
  for i,refList in enumerate(refered):
    print("Referer graph depth {}: {} requests".format(i, len(refList)))
    refDomains = set([TA.domainOf(url) for url in refList])
    refLetterTracker = set([d for d in refDomains if
                            d in engine.getAllTrackersOfType('ABCDEF')])
    
    print("{} tracker domains in the refered requests".format(len(refLetterTracker)))
    if secondEngine != None:
      refNotRequested = set([d for d in refLetterTracker if
                             d not in secondEngine.getAllTrackers()])
      refWasLetter = set([d for d in refLetterTracker if
                          d in secondEngine.getAllTrackersOfType('ABCDEF')])
      refWasReqButNotLetter = set([d for d in refLetterTracker if
                                   d in secondEngine.getAllTrackersOfType('3')
                                   and d not in refWasLetter])
      print("Of those, {} were trackers, {} were 3rd-party requests, and {} were not requested".format(
        len(refWasLetter), len(refWasReqButNotLetter), len(refNotRequested)))

def analyzeRefererGraphTopDown(engine, startingList, secondEngine=None, maxDepth=10):
  print("Starting list len {}".format(len(set(startingList))))
  refererGraphTopDown = buildRefererGraphDown(engine, startingList, maxDepth)
  print("{} first level len".format(len(refererGraphTopDown)))
  #TODO ANALYSIS

def analyzeRefererGraphBottomUp(engine, startingList, secondEngine=None, maxDepth=10):
  print("Starting list len {}, has {} trackers".format(len(startingList)))
  refererGraphBottomUp = buildRefererGraphUp(engine, startingList, maxDepth)
  print("{} first level len".format(len(refererGraphTopDown)))
  #TODO ANALYSIS

# Returns a list of the top numSites sites for that run        
def getOrderedTopNSites(mongo, run_name, numSites):
  r = mongo.hammer.run.find_one({'run_name': run_name})
  if r == None:
    return None
  if r['mode'] == 'Wayback':
    return [TA.domainOf(TA.getArchivedURLFromWaybackURL(u.strip())) for u in 
          r['wayback_urls_of_input'][0:numSites]]
  else:
    return [TA.domainOf(u.strip()) for u in r['input'][0:numSites]]

def getEventsFromTopNSites(mongo, run_name, numSites, eng):
  siteList = getOrderedTopNSites(mongo, run_name, numSites)
  eventsList = eng.processedEvents
  return [e for e in eventsList if 'top_url' in e and TA.domainOf(e['top_url']) in siteList]


######
# Historical sites utilities
######

def readHistoricalDF():
  historicalDF = pd.read_csv('historicalGraphData.csv', index_col='dataset')
  print("Dataframe opened of size: {}".format(len(historicalDF)))
  print(historicalDF.columns)
#historicalDF.drop('Unnamed: 0', axis=1, inplace=True)
#writeHistoricalDF()
  return historicalDF

def writeHistoricalDF(historicalDF):
  historicalDF.to_csv('historicalGraphData.csv', index=True)

def saveTablesToCSV(tables, year=None):
  if year != None:
    if year in tables:
      saveCSV(tables[year], 'historicalTables/'+str(year)+'table.csv')
    return
  for year, table in tables.items():
    saveCSV(table, 'historicalTables/'+str(year)+'table.csv')

def loadInHistoricalData(mongo, mongoHost, mongoPort, keyList, runNameList,
                         runNames={}, waybackTimes={}, engines={}, tables={},
                         overwriteHistoricalDicts=False,
                         printTables=False, updateMongoRun=False,
                         typeEFilenames=None):
  if len(keyList) != len(runNameList):
    print("ERROR keylist len {}, runName len {}, must be same".format(len(keyList), len(runNameList)))
    return False

  socialSet = set()
          
  for k, r in zip(keyList, runNameList):
    if not overwriteHistoricalDicts and k in engines and k in tables:
      print("Continuing past {}".format(k))
      continue

    if typeEFilenames != None:
      socialSet = set()
      with open(typeEFilenames[k], 'r') as socialF:
        for line in socialF:
          socialSet.add(line.strip())

    makeWbEngineForKey(mongo, mongoHost, mongoPort, k, r,
                       runNames, waybackTimes, engines, socialSet)
    print("Engine made for {}".format(k))
    printFullCombinedTypesTable(k, engines, tables, printTables, overwriteHistoricalDicts)
    if updateMongoRun:
      updateMongoRunWithEngine(mongo, r, engines[k], k)

  print("Loading of {} runs complete".format(len(keyList)))
  return runNames, waybackTimes, engines, tables

def serializeSitesTrackersTypesAsTypesSitesTrackers(engine):
  ret =  defaultdict(list)
  for s, v in engine.sitesToTrackersToTypes.items():
    for t, types in v.items():
      for ty in types:
        ret[ty].append((s, t))
  return ret        

def updateMongoRunWithEngine(mongo, run_name, engine, dfkey):
  mongoAble = serializeSitesTrackersTypesAsTypesSitesTrackers(engine)
  update = {'$set': {'dfKey': dfkey, 'types_sites_trackers': mongoAble}}
  #update2 ={'$set': {'trackers_to_sites_to_types': engine.trackersToSitesToTypes}}
  result = mongo.hammer.run.update_one({'run_name': run_name}, update)
  print("Updated run " + run_name)
                
def makeWbEngineForKey(mongo, mongoHost, mongoPort, key, run_name,
                       runNames, waybackTimes, engines, socialSet):
    runNames[key] = run_name
    waybackTimes[key] = mongo.hammer.run.find_one({'run_name': run_name})['wayback_time']
    engines[key] = TA.AnalysisEngine(wayback=True, waybackTime=waybackTimes[key], socialDomains=socialSet)
    engines[key].processEvents(TA.memoizedGetSortedEventsForRun(run_name, mongoHost, mongoPort))
    
def printTrackersAndSitesForKey(key):
  print("Information for run {} at date {}".format(runNames[key], waybackTimes[key]))
  print("{} trackers in dataset".format(len(engines[key].getAllTrackers())))
  print("{} sites with trackers in dataset".format(len(engines[key].getAllSitesWithTrackers())))
    
def printFullCombinedTypesTable(key, engines, tables, printTable=True, overwrite=False):
  if overwrite or key not in tables:
    tables[key] = []
    for s in engines[key].getAllSitesWithTrackers():
        for t in engines[key].getTrackersOnSite(s):
            tables[key].append([s, t, engines[key].getCombinedTypeOfTrackerOnSite(s, t)])
    saveTablesToCSV(tables, key)
  if printTable:
    print(tabulate(tables[key], headers=['Site', 'Tracker', 'Combined Tracker Type']))

# pulls trackers sites types and fixes them with new type E lists
# last two arguments are dicts
def fixTypeETrackers(mongo, runNames, typeEFilenames):
  for key, rname in runNames.items():
    socialSet = set()
    with open(typeEFilenames[key], 'r') as socialF:
      for line in socialF:
        socialSet.add(line.strip())
    run = mongo.hammer.run.find_one({'run_name': rname})
    typesSitesTrackers = run['types_sites_trackers']
    # check list of Bs and Cs and see if in social list
    eset = set()
    for ty in 'BC':
      if ty in typesSitesTrackers.keys():
        for s, t in typesSitesTrackers[ty]:
          if t in socialSet:
            eset.add((s, t))
    typesSitesTrackers['E'] = list(eset)
    
    update = {'$set': {'dfKey': key, 'types_sites_trackers': typesSitesTrackers}}
    result = mongo.hammer.run.update_one({'run_name': rname}, update)
    print("Updated run " + rname)
    
def resourceTypeCounting(eng):
  resourceTypeCounts = Counter()
  robotsCount = 0
  blockedCount = 0
  for e in eng.processedEvents:
    if 'resource_type' not in e:
      continue
    resourceTypeCounts[e['resource_type']] += 1
    if e['blocked'] == True:
      blockedCount += 1
      if 'response_code' in e and e['response_code'] == 403:
        robotsCount += 1
  pprint.pprint(resourceTypeCounts)
  print("{} blocked and {} robots".format(blockedCount, robotsCount))

  
###### GRAPH MAKING #######

# Expects a pandas dataframe where the columns include the things you want to graph
# Can convert a dict to a dataframe, see: http://pandas.pydata.org/pandas-docs/stable/10min.html
# example xColumnName='parallelism', yColumnName='responseFraction', colorColumnName='time_on_page'
# colorColumnName can be None if you only need 1 bar per x,y pair.
# pass a filename to save the figure ex "graphs/DescriptiveTitle.svg"
# ylim allows zooming in on part of the y axis

def barGraph(df, xColumnName, yColumnName, colorColumnName, 
             xaxisLabel, yaxisLabel, legendTitle, figTitle,
             size=4, order=None, filename=None, ylim=None, splitColName=None):
  sns.set_style("whitegrid")
  hue_order = None
  if colorColumnName != None:
    hue_order = sorted(set(df[colorColumnName]))
  
  g = sns.factorplot(x=xColumnName, y=yColumnName, hue=colorColumnName,
                     order=order, hue_order=hue_order,
                     col=splitColName, size=size,
                     data=df, kind="bar", legend=0, palette='colorblind')
  g.set_xlabels(xaxisLabel)
  g.set_ylabels(yaxisLabel)

  if splitColName == None:
    plt.title(figTitle)

  if ylim is not None:
    g.set(ylim=ylim)
  if colorColumnName != None:
    plt.legend(title=legendTitle, ncol=2, loc='upper left')
  if filename != None:
    plt.savefig(filename)

  plt.show()

# This kind of graph has numbers on both axes, so it only takes the list of numbers for the y axis.  If want to plot on a subplot, pass in a matplotlib axes object.
# TODO figure out how to do figure titles for subplots
def histGraph(listToGraph, xaxisLabel, filename=None, axes=None):
  x = pd.Series(listToGraph)
  sns.distplot(x, kde=False, rug=True, axlabel=xaxisLabel, ax=axes)
  
  if filename != None:
    plt.savefig(filename)
  if axes == None:
    plt.show()


def makeSubplotReturnAxes(howMany=2):
  plt.figure(num=1, figsize=(20,10))
  return (plt.subplot(howMany))


#####
# Specific Graphs
#####

def thirdReqsStats(thirdReqsValues, historicalDF, key, columnName, siteListLen):
  historicalDF.at[key, columnName+'mean'] = sum(thirdReqsValues)/siteListLen
  historicalDF.at[key, columnName+'min'] = min(thirdReqsValues)
  historicalDF.at[key, columnName+'max'] = max(thirdReqsValues)
  historicalDF.at[key, columnName+'median'] = numpy.median(list(thirdReqsValues))
  haveAtLeast1 = [c for c in thirdReqsValues if c > 0]
  meanAtLeast1 = 0
  if len(haveAtLeast1) > 0:
    meanAtLeast1 = sum(haveAtLeast1)/len(haveAtLeast1)
  historicalDF.at[key, columnName+'meanAtLeast1'] = meanAtLeast1
  return historicalDF

# Pass me either a dict of engines OR will use the mongo cache for runNames
def thirdPartyRequestsOverTime(numSites, columnName, historicalDF, mongo,
                               runNames, engines=None):
  if engines != None:
    for y, eng in engines.items():
      thirdReqs = Counter()
      siteList = getOrderedTopNSites(mongo, runNames[y], numSites)
      for s in siteList:
        thirdReqs[s] += eng.getNumTrackersOfTypeOnSites(s, '3')
      historicalDF = thirdReqsStats(thirdReqs.values(), historicalDF, int(y),
                                    columnName, len(siteList))

  else: # using mongo cache
    runNameList = [rn for rn in runNames.values() if 'types_sites_trackers' in mongo.hammer.run.find_one({'run_name': rn})]
    print(set(runNames.values()) - set(runNameList))
    print("{} runs being processed".format(len(runNameList)))
    for rname in runNameList:
      siteList = getOrderedTopNSites(mongo, rname, numSites)
      thirdReqs = Counter()
      for s in siteList:
        thirdReqs[s] = 0
      run = mongo.hammer.run.find_one({'run_name': rname})
      typesSitesTrackers = run['types_sites_trackers']
      if '3' in typesSitesTrackers:
        threes = typesSitesTrackers['3']
        for s, _ in threes:
          if s in siteList:
            thirdReqs[s] += 1
      else:
        print("No third parties here {}".format(rname))

      historicalDF = thirdReqsStats(thirdReqs.values(), historicalDF,
                                    int(run['dfKey']), columnName, len(siteList))
  historicalDF.sort(inplace=True)
  writeHistoricalDF(historicalDF)  
  return historicalDF

def thirdPartyReqsGraphs(numSites, historicalDF, mongo, runNames):
  numSitesStr = str(numSites)
  colName = "third_reqs_top_"+numSitesStr+"_"
  historicalDF = thirdPartyRequestsOverTime(numSites, colName, historicalDF,
                                            mongo, runNames)
  statsList = ['min', 'median', 'mean', 'max', 'meanAtLeast1']
  colList = [colName+stat for stat in statsList]
  dfSlice = historicalDF[historicalDF[colName+statsList[2]] > 0][colList]
  sns.set_style("whitegrid")
  figDim = len(dfSlice)/2
  #fig = plt.figure(figsize=(figDim, .5*figDim))
  fig = plt.figure(figsize=(10, 5))
  ax = fig.gca()
  plt.title('Third Parties Requested Per Site (Top {} Sites)'.format(numSitesStr), fontweight="bold", fontsize=22)

  my_colors = [(55,126,184),(77,175,74),(228,26,28),(152,78,163),(255,127,0),(166,86,40)]
  my_colors = [(r/255, g/255, b/255) for (r, g, b) in my_colors]
  my_dashes = [(None, None), [5,5], [5,3,2,3], [2,3], [5,2,5,2,5,10]] #,
               #[None, None] [1,2,1,10]]
  
  dfSlice.plot(kind='line', color=my_colors, ax=ax)
  ax.legend(statsList, bbox_to_anchor=[0, 1.02], loc=2, fontsize=14)
  for line, leg_line, i in zip(ax.get_lines(), ax.get_legend().get_lines(), range(len(my_dashes))):
    line.set_dashes(my_dashes[i])
    leg_line.set_dashes(my_dashes[i])
  plt.ylabel('Third Parties Requested per Site', fontweight="bold", fontsize=18)
  plt.xlabel('Year', fontweight="bold", fontsize=18)
  plt.xticks(dfSlice.index, fontweight="bold", fontsize=14, rotation='45', ha='right')
  plt.yticks(fontweight="bold", fontsize=14)
  fig.set_tight_layout(True)
  fig.savefig('graphs/overTime/thirdParties'+str(numSites)+'.png')

def slidesThirdReqGraphs(numSites, historicalDF, mongo, runNames):
  numSitesStr = str(numSites)
  colName = "third_reqs_top_"+numSitesStr+"_"
  historicalDF = thirdPartyRequestsOverTime(numSites, colName, historicalDF,
                                            mongo, runNames)
  statsList = ['max', 'meanAtLeast1', 'mean', 'median', 'min']
  colList = [colName+stat for stat in statsList]
  dfSlice = historicalDF[historicalDF[colName+statsList[2]] > 0][colList]
  sns.set_style("whitegrid")
  figDim = len(dfSlice)/2
  #fig = plt.figure(figsize=(figDim, .5*figDim))
  fig = plt.figure(figsize=(10, 5))
  ax = fig.gca()
  plt.title('Third Parties Requested Per Site (Top {} Sites)'.format(numSitesStr), fontweight="bold", fontsize=22)

  my_colors = [(55,126,184),(77,175,74),(228,26,28),(152,78,163),(255,127,0),(166,86,40)]
  my_colors = [(r/255, g/255, b/255) for (r, g, b) in my_colors]
  my_dashes = [(None, None), [5,5], [5,3,2,3], [2,3], [5,2,5,2,5,10]] #,
               #[None, None] [1,2,1,10]]
  
  dfSlice.plot(kind='line', color=my_colors, ax=ax, linewidth=3.0)
  ax.legend(statsList, bbox_to_anchor=[0, 1.02], loc=2, fontsize=14)
  #for line, leg_line, i in zip(ax.get_lines(), ax.get_legend().get_lines(), range(len(my_dashes))):
  #  line.set_dashes(my_dashes[i])
  #  leg_line.set_dashes(my_dashes[i])
  plt.ylabel('Third Parties Requested per Site', fontweight="bold", fontsize=18)
  plt.xlabel('Year', fontweight="bold", fontsize=18)
  plt.xticks(dfSlice.index, fontweight="bold", fontsize=14, rotation='45', ha='right')
  plt.yticks(fontweight="bold", fontsize=14)
  fig.set_tight_layout(True)
  fig.savefig('graphs/overTime/thirdParties'+str(numSites)+'.pdf')
  
# Pass me a dict of engines or will use run cache in mongo
def letterTrackingOverTime(numSites, historicalDF, mongo, runNames,
                           engines=None):
  if engines != None:
    for y, eng in engines.items(): 
      siteList = getOrderedTopNSites(mongo, runNames[y], numSites)
      for ty in "ABCDEF":
        setOfTrackers = set()
        columnName = ty+str(numSites)
        for s in siteList:
          setOfTrackers.add(eng.getTrackersOfTypeOnSites(s, ty))
        historicalDF.at[int(y), columnName] = len(setOfTrackers)
  else: # using mongo cache
    runNameList = [rn for rn in runNames.values()
                   if 'types_sites_trackers'
                   in mongo.hammer.run.find_one({'run_name': rn})]
    for rname in runNameList:
      siteList = getOrderedTopNSites(mongo, rname, numSites)
      run = mongo.hammer.run.find_one({'run_name': rname})
      typesSitesTrackers = run['types_sites_trackers']
      setOfTrackers = defaultdict(set)
      typeCTrackersSites = defaultdict(set)
      for ty in "FEDCBA":
        columnName = ty+str(numSites)
        if ty in typesSitesTrackers:
          pairsOfThatType = typesSitesTrackers[ty]
          for s, t in pairsOfThatType:
            if s in siteList:
              if ty != "B":
                setOfTrackers[ty].add(t)
                setOfTrackers['total'].add(t)
                if ty == "C":
                  typeCTrackersSites[t].add(s)
                elif ty == "E" and int(run['dfKey']) == 2006:
                  print("2006: {} is E on {}".format(t, s))
              elif s not in typeCTrackersSites[t] and t not in setOfTrackers["E"]:
                setOfTrackers["B"].add(t)
                setOfTrackers['total'].add(t)
                
        historicalDF.at[int(run['dfKey']), columnName] = len(setOfTrackers[ty])
      totalCol = 'TotalTrackingDomains'+str(numSites)
      historicalDF.at[int(run['dfKey']), totalCol] = len(setOfTrackers['total'])
  historicalDF.sort(inplace=True)
  writeHistoricalDF(historicalDF)  
  return historicalDF
  

def graphLetterTracking(numSites, historicalDF, mongo, runNames):
  numSitesStr = str(numSites)
  historicalDF = letterTrackingOverTime(numSites, historicalDF, mongo, runNames)
  statsList = ['A', 'B', 'C', 'D', 'E', 'F']
  typeNames = ['Analytics', 'Vanilla', 'Forced', 'Referred', 'Personal', 'Referred Anlytics']
  colList = [stat+numSitesStr for stat in statsList]
  dfSlice = historicalDF[historicalDF[colList[1]] >= 0][colList]
  dfSlice.columns = typeNames
  
  #Make a graph
  sns.set_style("whitegrid")
  figDim = len(dfSlice)/1.75
  fig, ax = plt.subplots(1, 1, figsize=(10, 6))
  my_colors = [(55,126,184),(77,175,74),(228,26,28),(152,78,163),(255,127,0),(166,86,40)]
  my_colors = [(r/255, g/255, b/255) for (r, g, b) in my_colors]
  my_dashes = [(None, None), [5,8], [5,3,2,3], [2,3], [5,2,5,2,5,10],
               [3,2,3,10], (None, None)]
  for ty, color, dash in zip(dfSlice.columns, my_colors, my_dashes):
    plt.plot(dfSlice.index, dfSlice[ty], color=color, dashes=dash, label=ty)
  width=.8
  plt.bar(historicalDF.index-width/2,
          historicalDF['TotalTrackingDomains'+numSitesStr],
          width, color=(211/255, 211/255, 211/255), label='Total Tracker Domains')
  #plt.xticks(numpy.arange(1, len(historicalDF)+1)+1/2, historicalDF.index)
  ax.set_title('Trackers of Each Type In Dataset (Top {} Sites)'.format(numSitesStr), fontweight="bold", fontsize=22)
  ax.set_ylabel('Trackers in Dataset', fontweight="bold", fontsize=18)
  ax.set_xlabel('Year', fontweight="bold", fontsize=18)
  ax.set_xticks(historicalDF.index)
  ax.set_xticklabels(historicalDF.index, rotation='45', fontweight="bold", fontsize=14)
  ax.set_yticklabels(ax.get_yticks().tolist(), fontweight="bold", fontsize=14)
  plt.xlim(dfSlice.index.values[0]-.5, dfSlice.index.values[-1]+.5)
  #ax.autoscale(axis='y', tight=True)
  ax.legend(loc=2, fontsize=14)
  fig.savefig('graphs/overTime/letterTrackingTop'+str(numSites)+'.png')
  
def graphLetterTrackingForSlides(numSites, historicalDF, mongo, runNames):
  numSitesStr = str(numSites)
  historicalDF = letterTrackingOverTime(numSites, historicalDF, mongo, runNames)
  statsList = ['A', 'B', 'C', 'D', 'E', 'F']
  typeNames = ['Analytics', 'Vanilla', 'Forced', 'Referred', 'Personal', 'Referred Anlytics']
  colList = [stat+numSitesStr for stat in statsList]
  dfSlice = historicalDF[historicalDF[colList[1]] >= 0][colList]
  dfSlice.columns = typeNames

  #Make a graph
  sns.set_style("whitegrid")
  figDim = len(dfSlice)/1.75
  fig, ax = plt.subplots(1, 1, figsize=(10, 6))
  my_colors = [(55,126,184),(77,175,74),(228,26,28),(152,78,163),(255,127,0),(166,86,40)]
  my_colors = [(r/255, g/255, b/255) for (r, g, b) in my_colors]
  my_dashes = [(None, None), [5,8], [5,3,2,3], [2,3], [5,2,5,2,5,10],
               [3,2,3,10], (None, None)]
  for ty, color, dash in zip(dfSlice.columns, my_colors, my_dashes):
    plt.plot(dfSlice.index, dfSlice[ty], color=color, label=ty, linewidth=3.0)
  width=.8
  plt.bar(historicalDF.index-width/2,
          historicalDF['TotalTrackingDomains'+numSitesStr],
          width, color=(211/255, 211/255, 211/255), label='Total Tracker Domains')
  #plt.xticks(numpy.arange(1, len(historicalDF)+1)+1/2, historicalDF.index)
  ax.set_title('Trackers of Each Type In Dataset (Top {} Sites)'.format(numSitesStr), fontweight="bold", fontsize=22)
  ax.set_ylabel('Trackers in Dataset', fontweight="bold", fontsize=18)
  ax.set_xlabel('Year', fontweight="bold", fontsize=18)
  ax.set_xticks(historicalDF.index)
  ax.set_xticklabels(historicalDF.index, rotation='45', fontweight="bold", fontsize=14)
  ax.set_yticklabels(ax.get_yticks().tolist(), fontweight="bold", fontsize=14)
  plt.xlim(dfSlice.index.values[0]-.5, dfSlice.index.values[-1]+.5)
  #ax.autoscale(axis='y', tight=True)
  ax.legend(loc=2, fontsize=14)
  fig.set_tight_layout(True)
  fig.savefig('graphs/overTime/letterTrackingForSlide'+str(numSites)+'.pdf')
  
# numSites is how many top sites
# engines is a dict of engines, keyed by dataset
# runNames is a dict of run_name strings, keyed by dataset
# historicalDF is a DataFrame indexed (row names) by a key representing the
# dataset (ex 1996, 2002WaPo)
def popupsOverTime(numSites, mongo, engines, runNames, historicalDF=pd.DataFrame()):
  popupWindowIDs = defaultdict(set)
  for y, eng in engines.items():
    for e in getEventsFromTopNSites(mongo, runNames[y], numSites, eng):
      if 'window_type' in e and e['window_type'] == 'popup':
        popupWindowIDs[y].add(e['window']['id'])
    historicalDF.at[int(y), 'Popup'+str(numSites)] = len(popupWindowIDs[y])
  writeHistoricalDF(historicalDF)
  return historicalDF

def notAlexaPopupsOverTime(numSites, mongo, engines, runNames, historicalDF=pd.DataFrame()):
  popupWindowIDs = defaultdict(set)
  for y, eng in engines.items():
    for e in getEventsFromTopNSites(mongo, runNames[y], numSites, eng):
      if 'window_type' in e and e['window_type'] == 'popup':
        if e['top_url'] not in getOrderedTopNSites(mongo, runNames[y], numSites, eng):
          popupWindowIDs[y].add(e['window']['id'])
    historicalDF.at[int(y), 'Popup'+str(numSites)] = len(popupWindowIDs[y])
  writeHistoricalDF(historicalDF)
  return historicalDF

# numSites is how many top sites
# engines is a dict of engines, keyed by dataset
# runNames is a dict of run_name strings, keyed by dataset
# historicalDF is a DataFrame indexed (row names) by a key representing the
# dataset (ex 1996, 2002WaPo)
def iframesOverTime(numSites, mongo, engines, runNames, historicalDF=pd.DataFrame(), live=False):
  iframeFrameIDs = defaultdict(set)
  for y, eng in engines.items():
    for e in getEventsFromTopNSites(mongo, runNames[y], numSites, eng):
      if 'from_subframe' in e and e['from_subframe']:
        print('frame' in e and 'id' in e['frame'])
        if 'frame' in e and e['frame'] != None and 'id' in e['frame'] and e['frame']['id'] != None:
          iframeFrameIDs[y].add(e['frame']['id'])
    key = y
    if not live:
      key = int(key)
    historicalDF.at[key, 'IFrame'+str(numSites)] = len(iframeFrameIDs[y])
    #writeHistoricalDF(historicalDF)
  return historicalDF

# gets the set of types each tracker has on the given sites
# typeList should be a list of approved types ex ['B', '3']
# siteList should probably come from getOrderedTopNSites(mongo, run_name, numSites)
def convertTypesCacheToTrackersToTypes(run_name, mongo, typeList, siteList):
  run = mongo.hammer.run.find_one({'run_name': run_name})
  if 'types_sites_trackers' not in run:
    return None
  typesSitesTrackers = run['types_sites_trackers']
  trackersToTypes = defaultdict(set)
  
  #if only ever see BC for tracker, then it's a C but if it's ever a B without a C then it is both
  #E's are never B's
  #reverse the list so that we're looking at B's after E's and C's

  typeCTrackerToSites = defaultdict(set)

  typesToCheck = [ty for ty in sorted(typeList, reverse=True)
                  if ty in typesSitesTrackers]
  for ty in typesToCheck:
    for s, t in typesSitesTrackers[ty]:
      if s in siteList:
        if ty != 'B':
          trackersToTypes[t].add(ty)
          if ty == 'C':
            typeCTrackerToSites[t].add(s)
        elif 'E' not in trackersToTypes[t] and s not in typeCTrackerToSites[t]:
          trackersToTypes[t].add('B')
  return trackersToTypes

def quantityOfTypesDistribution(numSites, historicalDF, mongo, runNames,
                                engines=None, include3=False, live=False):
  typeList = ['A', 'B', 'C', 'D', 'E', 'F']
  colSuffix = 'Type_'+str(numSites)
  if include3:
    typeList.append('3')
    colSuffix += '_with3'
  runNameList = [rn for rn in runNames.values()
                 if 'types_sites_trackers'
                 in mongo.hammer.run.find_one({'run_name': rn})]
  multipleTypeCounter = defaultdict(Counter)
  for rname in runNameList:
    if not live:
      key = int(mongo.hammer.run.find_one({'run_name': rname})['dfKey'])
    else:
      key = mongo.hammer.run.find_one({'run_name': rname})['dfKey']
    siteList = getOrderedTopNSites(mongo, rname, numSites)
    trackersToTypes = convertTypesCacheToTrackersToTypes(rname, mongo,
                                                         typeList, siteList)
    #tracker->TypeSet -> tracker->len(typeSet) -> len(typeSet)->len(trackerSet)
    # just make this a table
    
    totalTrackers = len(trackersToTypes)
    valueCounter = defaultdict(int)
    multipleTypeCounter[key] = Counter()
    for t, v in trackersToTypes.items():
      valueCounter[len(v)] += 1
      if len(v) > 1:
        multipleTypeCounter[key]["".join(v)] += 1
    for n in range(1, 1+len(typeList)):
      colName = str(n)+colSuffix
      valToInput = 0
      if totalTrackers > 0:
        num = valueCounter[n]
        if num > 0:
          valToInput = "{:.2%} ({})".format(num/totalTrackers, num)
      historicalDF.at[key, colName] = valToInput
  #writeHistoricalDF(historicalDF)
  return historicalDF, multipleTypeCounter

def tableQuantityOfTypes(numSites, myDF, mongo, runNames, live=False):
  myDF, multipleTypes = quantityOfTypesDistribution(numSites, myDF, mongo, runNames, include3=False, live=live)
  print("Top {}".format(numSites))
  for k in sorted(multipleTypes.keys()):
    if len(multipleTypes[k]) > 0:
      print("{}: {}".format(k, multipleTypes[k].most_common()))
  colNames = [str(n)+'Type_'+str(numSites) for n in range(1,5)] #no3
  if not live:
    keyList = [int(k) for k in runNames.keys()]
  else:
    keyList = runNames.keys()
  dfSlice = myDF[myDF.index.isin(keyList)]
  dfSlice = dfSlice.loc[:, colNames]
  with open('graphs/overTime/typeDistributionTop{}.tex'.format(numSites), 'w') as outfile:
    outfile.write(tabulate(dfSlice, headers=['Year']+[i[0:5] for i in colNames], tablefmt="latex"))
  print(tabulate(dfSlice, stralign="right", headers=['Year']+[i[0:5] for i in colNames]))

def graphQuantityOfTypes(numSites, historicalDF, mongo, runNames, live=False):
  historicalDF = quantityOfTypesDistribution(numSites, historicalDF, mongo, runNames, include3=True, live=live)
  colNames = [str(n)+'Type_'+str(numSites)+'_with3' for n in range(1,8)] #with3
  if not live:
    keyList = [int(k) for k in runNames.keys()]
  else:
    keyList = runNames.keys()
  dfSlice = historicalDF[historicalDF.index.isin(keyList)]
  dfSlice = dfSlice.loc[:, colNames]

  historicalDF = quantityOfTypesDistribution(numSites, historicalDF, mongo, runNames, include3=False, live=live)

  #print(historicalDF)
  colNames = [str(n)+'Type_'+str(numSites) for n in range(1,7)] #no3
  dfSlice2 = historicalDF[historicalDF.index.isin(keyList)]
  dfSlice2 = dfSlice2.loc[:, colNames]

  f, (ax1, ax2) = plt.subplots(1, 2, sharey=True,
                               figsize=(len(dfSlice), .3*len(dfSlice)))
  f.suptitle("What Fraction of Trackers Have Multiple Types? (Top {} Sites)".format(numSites))
  
  dfSlice.plot(kind='bar', stacked=True, ax=ax1, legend=False)
  ax1.set_title('With third-party requests as type')

  dfSlice2.plot(kind='bar', stacked=True, ax=ax2, legend=False)
  ax2.set_title('Without third-party requests')

  f.savefig('graphs/overTime/fractionOfTypeQuantityTop{}.svg'.format(numSites))

def thirdCDF(mongo, numSites, runNames, historicalDF):
  # eventually want a number of trackers (0-max ever seen+1)-> % of domains per year 
  # (% of domains just means dividing by total # of domains)
    # year is still index. Columns for each number of trackers? Yikes.
  runNameList = [rn for rn in runNames.values() 
                 if 'types_sites_trackers' in mongo.hammer.run.find_one({'run_name': rn})]
  print("{} runs being processed".format(len(runNameList)))
  beforePercentsTable = defaultdict(list)
  maxNumDomainsOnSite = 0
  for rname in runNameList:
    siteList = getOrderedTopNSites(mongo, rname, numSites)
    thirdReqs = Counter()
    for s in siteList:
      thirdReqs[s] = 0
    run = mongo.hammer.run.find_one({'run_name': rname})
    typesSitesTrackers = run['types_sites_trackers']
    if '3' in typesSitesTrackers:
      threes = typesSitesTrackers['3']
      for s, _ in threes:
        if s in siteList:
          thirdReqs[s] += 1
    # now I have a counter with the number of thirdReqs for each site that year
    # counter most_common gives me the largest count
    key = int(run['dfKey'])
    totalSites = len(siteList)
    mostCommonCount = thirdReqs.most_common(1)[0][1]
    maxNumDomainsOnSite = max(maxNumDomainsOnSite, mostCommonCount)
    #print(mostCommonCount)
    howManyDomainsWithThirdCount = defaultdict(int)
    for (s, numThirdReqs) in thirdReqs.most_common():
      howManyDomainsWithThirdCount[numThirdReqs] += 1
      #print("{} {}".format(key, howManyDomainsWithThirdCount))
    # so now what I have is the count of how many domains have each tracker number
    # to get how many have at least each tracker number add the sum of everything greater
    howManyDomainsWithAtLeastThirdCount = defaultdict(int)
    for n in reversed(range(1+mostCommonCount)):
      howManyDomainsWithAtLeastThirdCount[n] = howManyDomainsWithThirdCount[n] + howManyDomainsWithAtLeastThirdCount[n+1]
    beforePercentsTable[key] = [(n, v) for n, v
                                in howManyDomainsWithAtLeastThirdCount.items()]
    #historicalDF.at[key, "AtLeast0Capable_"+str(numSites)] = 100.0
    for thirdCount, numDomains in howManyDomainsWithAtLeastThirdCount.items():
      historicalDF.at[key, "AtLeast{}Capable_{}".format(thirdCount, numSites)] = 100*numDomains/totalSites
    historicalDF.at[key, "AtLeast0Capable_"+str(numSites)] = 100.0
    historicalDF.at[key, "AtLeast{}Capable_{}".format(mostCommonCount+1, numSites)] = 0.0
  beforePercentsTableItems = beforePercentsTable.items()
  rawDF = pd.DataFrame({'Year': [k for k,_ in beforePercentsTableItems],
                        'NumTracker, HowManyDomainsHaveAtLeastNumTrackerTrackers': [v for _,v in beforePercentsTableItems]
                       })
  #print(rawDF)
  rawDF.to_csv('graphs/rawReverseCDF_top{}.csv'.format(numSites))
  historicalDF.sort(inplace=True)
  #writeHistoricalDF(historicalDF)
  return historicalDF, maxNumDomainsOnSite+1
    
def graphReverseThirdPartyCDF(mongo, numSites, runNames, historicalDF, showOdd=False):
  historicalDF, maxColNumber = thirdCDF(mongo, numSites, runNames, historicalDF)
  print("Max col number: {}".format(maxColNumber))
  columnsToSlice = ["AtLeast{}Capable_{}".format(i, numSites) for i in range(1+maxColNumber)]
  dfSlice = historicalDF[historicalDF[columnsToSlice[0]] > 0][columnsToSlice]
  dfSlice.columns = range(1+maxColNumber)
  #print(dfSlice.columns)
  sns.set_style("whitegrid")
  #figDim = len(dfSlice)/1.5
  fig = plt.figure(figsize=(9, 5))
  ax = fig.gca()
  plt.title('Distribution of Included Trackers (Top {} Sites)'.format(numSites), fontweight="bold", fontsize=22)
  plt.ylabel('Percentage of Sites', fontweight="bold", fontsize=18)
  plt.xlabel('Minimum Number of Trackers', fontweight="bold", fontsize=18)
  if showOdd:
    howManyYears = len([y for y in dfSlice.index.values if y % 2 == 1])
  else:
    howManyYears = len(dfSlice.index.values)
  my_colors = sns.cubehelix_palette(howManyYears, light=.7, rot=-1.2, reverse=True)
  my_dashes = [(None,None), [5,5], [5,3,2,3], [2,3], [5,2,5,2,5,10],
               [5,3,1,2,1,10], [1,2,1,10], [5, 3, 2, 10],
               (None, None), [5, 5], [5,3,2,3], [2,3], [5,2,5,2,5,10],
               [5,3,1,2,1,10], [1,2,1,10],[5,3,2,10]]
  for year, i in zip(dfSlice.index.values, range(2*len(my_colors))):
    if not showOdd:
      dfSlice2 = dfSlice.loc[year, :]
      dfSlice2.plot(kind='line', color=my_colors[i], label=year)
    elif year % 2 == 1:
      dfSlice2 = dfSlice.loc[year, :]
      dfSlice2.plot(kind='line', color=my_colors[int(math.floor(i/2))],
                    label=year)
  plt.xticks(fontweight="bold", fontsize=14) #rotation='45', ha='right')
  plt.yticks(fontweight="bold", fontsize=14)  
  ax.legend(loc='upper right', fontsize=12)
  ##plt.xticks(dfSlice.index) #, rotation='45')
  fig.savefig('graphs/overTime/thirdPartiesCDF'+str(numSites)+'.png')
