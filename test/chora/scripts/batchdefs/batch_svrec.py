import choraconfig, glob, os.path, re, sys

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"rec-svcomp-v19/")
batch["files"] = list()
for adir, dirs, files in os.walk(batch["root"]) :
    for filename in sorted(files) :
        path = os.path.join(adir,filename)
        if not path.endswith(".c") : continue
        if not "true-unreach-call" in path : continue
        batch["files"].append(path)
        
batch["format_style"] = "assert"

batch["timeout"] = 900

#batch["toolIDs"] = ["chorafull","icra2019","ua","utaipan","viap"] # artifact
batch["toolIDs"] = ["chorafull","icra2019"] # submission: use published results for other tools

