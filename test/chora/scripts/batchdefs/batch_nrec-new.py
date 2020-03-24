import choraconfig, glob, os.path, re, sys

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"nrec-new")
batch["files"] = glob.glob(batch["root"] + "/*.c")
batch["format_style"] = "assert"
batch["timeout"] = 900
#batch["toolIDs"] = ["chorafull","icra2019","ua","utaipan","viap"] # artifact
batch["toolIDs"] = ["chorafull","icra2019"] # submission: use published results for other tools
