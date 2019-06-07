import choraconfig, glob

batch = choraconfig.clone_batch("icra")

batch["toolIDs"] = ["chora"]
batch["timeout"] = 30
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
