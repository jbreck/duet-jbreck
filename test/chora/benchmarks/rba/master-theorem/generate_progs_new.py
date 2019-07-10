import subprocess
import os
import math


template_dir = "new-template"
outers = ["one","two","three","four","five"]
inners = ["two","three","four","five"]
adds = ["const","lin","quad","cub","quar","quin"]

def writeLoop(outfile, degree, typ):
    template = open(template_dir + "/" + adds[degree] + typ + ".tmp")
    for line in template:
        outfile.write(line)
    outfile.write("\n")
    template.close()


def createFile(target, a, b, degree, typ):
    outfile = open(target, "w+")
    outfile.write("int __cost = 0;\n\n")
    if (degree != 0 and typ != "") :
        writeLoop(outfile, degree, typ)
    outfile.write("void recursive(int n) {\n")
    #outfile.write("  __VERIFIER_assume (n >= 0);\n")
    terminating_cond = " || ".join(["n == " + str(i) for i in range(b, 2*b)])
    outfile.write("  if (" + terminating_cond + ") {\n")
    if (degree != 0):
        outfile.write("    __cost += " + str(2*b-1) + ";\n")
    else :
        outfile.write("    __cost++;\n")
    outfile.write("    return;\n")
    outfile.write("  }\n")
    outfile.write("  int m = n/" + str(b) + ";\n")
    for i in range(0, a):
        outfile.write("  recursive(m);\n")
    if (typ == ""):
        if (degree == 0):
            outfile.write("  __cost++;\n")
        elif (degree == 1):
            outfile.write("  __cost+=m;\n")
        elif (degree == 2):
            outfile.write("  __cost+=m*m;\n")
        elif (degree == 3):
            outfile.write("  __cost+=m*m*m;\n")
        elif (degree == 4):
            outfile.write("  __cost+=m*m*m*m;\n")
        else :
            outfile.write("  __cost+=m*m*m*m*m;\n")
    else :
        outfile.write("  loop(m);\n")
    outfile.write("  return;\n")
    outfile.write("}\n\n")
    outfile.write("void main(int n) {\n")
    outfile.write("  recursive(n);\n")
    outfile.write("}\n")
    outfile.close()




for outerval, outer in enumerate(outers):
    for innerval, inner in enumerate(inners):
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
                target = case + "/a-"+outer+"/b-" + inner + "/add-" +add+"/a_"+outer+"_b_"+inner+"_add_"+add+".c"
                createFile(target, outerval+1, innerval+2, degree, "") 
            else :
                types = ["","_rec","_loop"]
                for typ in types:
                    target = case + "/a-"+outer+"/b-" + inner + "/add-" +add+"/a_"+outer+"_b_"+inner+"_add_"+add+typ+".c"
                    createFile(target, outerval+1, innerval+2, degree, typ) 
