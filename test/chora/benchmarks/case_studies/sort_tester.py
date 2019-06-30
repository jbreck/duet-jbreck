#!/usr/bin/python

import subprocess, sys, os.path, random

if len(sys.argv) < 2 :
    print "USAGE: sort_tester.py <c program that sorts>"
    sys.exit(0)

sorter = sys.argv[1]
if not os.path.exists(sorter) :
    print "Could not find: " + sorter
    sys.exit(0)

exe = "deleteme_sorter"
if os.path.exists(exe) : os.remove(exe)
subprocess.call(["gcc",sorter,"-DTRYME","-o",exe])
print "Beginning tests.  Use Ctrl-C to exit."
while True :
    n = random.choice(range(36))
    if n == 0 : continue
    ints = [random.choice(range(100)) for I in range(n)]
    sys.stdout.write(str(ints))
    text = subprocess.check_output([exe] + [str(I) for I in ints])
    result = [int(S) for S in text.strip().split(" ")]
    if result != sorted(ints) : 
        print ""
        print "  --> Gave incorrect output: " + str(text)
        print ""
    else :
        sys.stdout.write("\r" + 150 * " " + "\r")

os.remove(exe)
