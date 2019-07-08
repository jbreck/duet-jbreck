import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"icrasuite/sv-benchmarks/")
batch["files"] = glob.glob(batch["root"] + "recursive/*.c") # just the "recursive/" directory is listed here for now
batch["files"] = batch["files"][4:6] # Just picking numbers 4-6 out of that directory for this quick test
batch["format_style"] = "assert"
batch["timeout"] = 60 # probably want much longer than this
batch["toolIDs"] = ["chora","icra","cpaseq","sea"] # everntually add SEA
