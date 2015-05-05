#!/usr/bin/env python3

import os
import sys
import glob
import tempfile
import threading
import itertools
import subprocess
from io import BytesIO
import multiprocessing.dummy

TIMEOUT = 240
NB_THREADS = 5

if sys.version_info < (3, 3, 0):
    print('Python >= 3.3 is needed (subprocess timeout support).')
    exit(3)

if len(sys.argv) == 2:
    ES5_ENV = sys.argv[1]
elif len(sys.argv) == 1:
    ES5_ENV = None
else:
    prog = sys.argv[0]
    print('Syntax: (any of the following)')
    print('\t%s' % prog)
    print('\t%s <env dump>' % prog)
    exit(2)

TEST_DIR = os.path.dirname(__file__)
EXE = os.path.join(TEST_DIR, "js")

def strip_extension(filename):
    return filename[0:-len('.in.ljs')]
def list_tests(dirname):
    return map(lambda x:tuple(x.split(".in.")), glob.glob(os.path.join(TEST_DIR, dirname, '*.in.*')))

tests = list_tests('no-env')
if ES5_ENV:
    tests = itertools.chain(tests, list_tests('es5'))

output_lock = threading.Lock()

successes = []
fails = []
skipped = []
timeout = []
def run_test(test, ext):
    global successes, fails, skipped
    in_ = test + '.in.' + ext
    out = test + '.out'
    skip = test + '.skip'
    if os.path.isfile(skip):
        with open(skip) as fd:
            skipped.append((test, fd.read()))
        with output_lock:
            print('%s: skipped.' % test)
        return
    if ext == "ljs":
        command = [EXE, '-ljs']
    else:
        command = [EXE]
    with open(in_) as in_fd:
        try:
            output = subprocess.check_output(command + [in_],
                stdin=in_fd, stderr=subprocess.DEVNULL, timeout=TIMEOUT)
        except subprocess.CalledProcessError:
            fails.append(test)
            return
    with tempfile.TemporaryFile() as out_fd:
        out_fd.write(output)
        out_fd.seek(0)
        with output_lock:
            sys.stdout.write('%s: ' % test)
            sys.stdout.flush()
            if subprocess.call(['diff', '-', out], stdin=out_fd):
                fails.append(test)
            else:
                successes.append(test)
                print('ok.')


stop = False
def test_wrapper(args):
    test = args[0]
    global stop
    try:
        if stop:
            return
        run_test(*args)
    except subprocess.TimeoutExpired:
        with output_lock:
            print('%s: timeout' % test)
        timeout.append(test)
    except Exception as e:
        stop = True
        raise

try:
    pool = multiprocessing.dummy.Pool(NB_THREADS)
    pool.map(test_wrapper, tests)
    for test in tests:
        threading.Thread(target=test_wrapper, args=test).start()
finally:
    with output_lock:
        print('')
        print('Result:')
        print('\t%d successed' % len(successes))
        print('\t%d skipped:' % len(skipped))
        for (test, msg) in skipped:
            print('\t\t%s: %s' % (test, msg))
        print('\t%d timed out:' % len(timeout))
        for test in timeout:
            print('\t\t%s' % test)
        print('\t%d failed:' % len(fails))
        for fail in fails:
            print('\t\t%s' % fail)
if fails:
    exit(1)
else:
    exit(0)

