import subprocess
import os
import math


def createFile(source, target, outerval, innerval):
    with open(source) as search:
        outfile = open(target, "w+")
        for line in search:
            if (line.strip() == ("recursive(n/2);")):
                for i in range(0, outerval+1):
                    outfile.write("    recursive(n/"+str(innerval+2)+");\n")
            #elif ("n <= 1" in line):
            #    terminating_cond = " || ".join(["n == " + str(i+1) for i in range(0, innerval+2)])
            #    newline = line.replace("n <= 1", terminating_cond)
            #    outfile.write(newline)
            else:
                outfile.write(line)
        search.close()
        outfile.close()



outers = ["one","two","three","four","five"]

for outerval, outer in enumerate(outers):
    #if (outerval != 0):
    #    subprocess.run(["mkdir", "a-" + outer])
    inners = ["two","three","four","five"]
    for innerval, inner in enumerate(inners):
        #if (outerval !=0 or innerval != 0):
            #subprocess.run(["mkdir", "a-" + outer + "/b-" + inner])
        adds = ["const","lin","quad","cub","quar","quin"]
        for degree, add in enumerate(adds):
            case = "case"
            if (outerval == 0):
                if (degree == 0):
                    case = case + "2"
                else:
                    continue
            elif (math.log(outerval+1,innerval+2) > degree):
                case = case + "1"
            elif (math.log(outerval+1,innerval+2) == degree):
                case = case + "2"
            elif (math.pow(innerval+2,degree)>(outerval+1)):
                case = case + "3"
            else:
                continue
            if (not os.path.isdir(case)):
                subprocess.run(["mkdir", case])
            if (not os.path.isdir(case+"/a-"+outer)):
                subprocess.run(["mkdir", case + "/a-"+outer])
            if (not os.path.isdir(case+"/a-"+outer+"/b-"+inner)):
                subprocess.run(["mkdir", case+"/a-"+outer+"/b-"+inner])
            if (not os.path.isdir(case+"/a-"+outer+"/b-"+inner+"/add-"+add)):
                subprocess.run(["mkdir", case+"/a-"+outer+"/b-"+inner+"/add-"+add])
            if (add == "const"):
                source = "template/a-one/b-two/add-" +add+"/a_one_b_two_add_"+add+".c"
                target = case + "/a-"+outer+"/b-" + inner + "/add-" +add+"/a_"+outer+"_b_"+inner+"_add_"+add+".c"
                createFile(source, target, outerval, innerval) 
            else :
                types = ["","_rec","_loop"]
                for typ in types:
                    source = "template/a-one/b-two/add-" +add+"/a_one_b_two_add_"+add+typ+".c"
                    target = case + "/a-"+outer+"/b-" + inner + "/add-" +add+"/a_"+outer+"_b_"+inner+"_add_"+add+typ+".c"
                    createFile(source, target, outerval, innerval) 
