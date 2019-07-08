import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"sv-comp/")
batch["files"] = list()
for adir, dirs, files in os.walk(batch["root"]) :
    batch["files"] += glob.glob(adir + "/*true-unreach*.c")
print(batch["files"])
#batch["files"] = batch["files"][4:6] # Just picking numbers 4-6 out of that directory for this quick test
batch["format_style"] = "assert"
batch["timeout"] = 60 # probably want much longer than this
batch["toolIDs"] = ["chora","icra","cpaseq","sea"] # everntually add SEA
