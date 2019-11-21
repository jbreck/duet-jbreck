import choraconfig, glob, os.path, re, sys

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"rec-svcomp-v19/")
#batch["root"] = os.path.join(choraconfig.benchroot,"easy-rec-svcomp-v19/")
#batch["root"] = os.path.join(choraconfig.benchroot,"svcomp2019/")
#batch["root"] = os.path.join(choraconfig.benchroot,"sv-comp/")
#batch["root"] = "/nobackup/jbreck/sv-benchmarks/c/"
batch["files"] = list()
for adir, dirs, files in os.walk(batch["root"]) :
    for filename in sorted(files) :
        path = os.path.join(adir,filename)
        if not path.endswith(".c") : continue
        #
        if not "true-unreach-call" in path : continue
        batch["files"].append(path)
        #
        #ymlpath = path.replace(".c",".yml")
        #if not os.path.exists(ymlpath) : continue
        #with open(ymlpath,"rb") as ymlfile : ymldata = ymlfile.read().replace("\n"," ")
        #regex =  "-\s+property_file:\s+../properties/unreach-call.prp\s+expected_verdict:\s+true"
        #matches = re.search(regex, ymldata)
        #if matches :
        #    batch["files"].append(path)
print "Files in this batch: "
print(batch["files"])
print " (end of file list)"
batch["format_style"] = "assert"

#batch["timeout"] = 100 # may want something longer than this
#print "WARNING: using short 100-second timeout"

batch["timeout"] = 900 # may want something longer than this
#batch["toolIDs"] = ["chora","icra2019","ua","utaipan","viap","veriabs"]
batch["toolIDs"] = ["chora","icra2019","viap","veriabs"]


