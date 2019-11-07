import choraconfig, glob, os.path, re, sys

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"svcomp2019/")
#batch["root"] = os.path.join(choraconfig.benchroot,"sv-comp/")
#batch["root"] = "/nobackup/jbreck/sv-benchmarks/c/"
batch["files"] = list()
for adir, dirs, files in os.walk(batch["root"]) :
    print adir
    if adir.endswith("/") : adir = adir[:-1]
    for okdir in [# Loop benchmarks
                  "loops",
                  "loop-acceleration",
                  "loop-crafted",
                  "loop-invgen",
                  "loop-lit",
                  "loop-new",
                  "loop-industry-pattern",
                  "loops-crafted-1",
                  "loop-invariants",
                  "loop-simple",
                  "verifythis-loops",
                  "nla-digbench",
                  # Recursive benchmarks
                  "recursive",
                  "recursive-simple",
                  "recursive-with-pointer",
                  "verifythis-recursive",
                ] :
        if adir.endswith(okdir) : break
    else :
        continue
    #
    for filename in sorted(files) :
        path = os.path.join(adir,filename)
        if not path.endswith(".c") : continue
        ymlpath = path.replace(".c",".yml")
        if not os.path.exists(ymlpath) : continue
        with open(ymlpath,"rb") as ymlfile : ymldata = ymlfile.read().replace("\n"," ")
        regex =  "-\s+property_file:\s+../properties/unreach-call.prp\s+expected_verdict:\s+true"
        #print ymldata
        matches = re.search(regex, ymldata)
        if matches :
            #print path
            batch["files"].append(path)
    #batch["files"] += glob.glob(adir + "/*true-unreach*.c")
print(batch["files"])
#batch["files"] = batch["files"][4:6]
batch["format_style"] = "assert"
batch["timeout"] = 300 # may want something longer than this
batch["toolIDs"] = ["chora","icra2019","cpaseq","sea"]
