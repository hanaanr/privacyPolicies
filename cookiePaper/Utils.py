import resource
import cProfile
import pstats
import time

def memory():
    GIG = 1024 * 1024 * 1024
    MEG = 1024 * 1024
    print('Using %f gigs' % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / GIG))
    print('Using %f megs' % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / MEG))

def timefunc(f):
    def f_timer(*args, **kwargs):
        start = time.time()
        result = f(*args, **kwargs)
        end = time.time()
        print(f.__name__, 'took', end - start, 'time')
        return result
    return f_timer


def do_cprofile(func):
    def profiled_func(*args, **kwargs):
        profile = cProfile.Profile()
        try:
            profile.enable()
            result = func(*args, **kwargs)
            profile.disable()
            return result
        finally:
            stats = pstats.Stats(profile)
#            profile.print_stats()
            stats.sort_stats('cumulative').print_stats(50)
    return profiled_func
