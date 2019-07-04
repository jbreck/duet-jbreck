import sys, math

outers = ["one","two","three","four","five"]
inners = ["two","three","four","five"]
adds = ["const","lin","quad","cub","quar","quin"]

filename = sys.argv[1]
vals = filename.split('_')
astr = vals[1]
bstr = vals[3]
degstr = (vals[5].split('.'))[0]

a = outers.index(astr) + 1
b = inners.index(bstr) + 2
deg = adds.index(degstr)

case = 0
if (a == 1):
    if (deg == 0):
        case = 2
    else :
        case = 3
elif (math.log(a, b) > deg):
    case = 1
elif (math.log(a, b) == deg):
    case = 2
else :
    case =3


if (case == 1) : 
    print("Case 1: log_" + str(b) + "(" + str(a)+ ") > " + str(deg))
    if (math.log(a, b)==1) :
        print("o(n)")
        print("O(n)")
    else :
        print("o(n^"+str(math.log(a,b)) + ")")
        print("O(n^"+str(math.log(a,b)) + ")")
elif (case == 2 and deg == 0) : 
    print("Case 2: log_" + str(b) + "(" + str(a)+ ") == " + str(deg))
    print("o(log_(n))")
    print("O(log_(n))")
elif (case == 2) : 
    print("Case 2: log_" + str(b) + "(" + str(a)+ ") == " + str(deg))
    if (deg == 1):
        print("o(n*log_(n))")
        print("O(n*log_(n))")
    else :
        print("o(n^"+str(deg) + "*log_(n))")
        print("O(n^"+str(deg) + "*log_(n))")
elif (case == 3) : 
    print("Case 3: log_" + str(b) + "(" + str(a)+ ") < " + str(deg))
    if (deg == 1):
        print("o(n)")
        print("O(n)")
    else: 
        print("o(n^"+str(deg) + ")")
        print("O(n^"+str(deg) + ")")

