import choraconfig, glob, os.path, re, sys

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"nrec-rba")
batch["files"] = glob.glob(batch["root"] + "/*.c")
batch["format_style"] = "rba"
batch["timeout"] = 60
batch["toolIDs"] = ["chora","icra2019c"]
