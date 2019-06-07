import choraconfig, glob

batch = choraconfig.get_default_batch_dict()

batch["files"] = glob.glob(choraconfig.benchroot + "assert/chora_simple/*.c")
batch["format_style"] = "assert"
batch["instant_unsound_callouts"] = True

