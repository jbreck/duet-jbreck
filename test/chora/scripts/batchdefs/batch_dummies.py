import choraconfig, glob, os.path, re, sys

batch = choraconfig.get_default_batch_dict()

# This is a batch consisting of only two SV-COMP benchmarks,
#   where were specifically chosen to be easy; one has the
#   result True, and the other False.  The idea is that you
#   can run tools against this batch to quickly check and
#   troubleshoot their configurations.

batch["root"] = os.path.join(choraconfig.benchroot,"dummies")
batch["files"] = glob.glob(batch["root"] + "/*.c")
batch["format_style"] = "assert"
batch["timeout"] = 60
batch["toolIDs"] = ["chora","icra2019","sea"]
