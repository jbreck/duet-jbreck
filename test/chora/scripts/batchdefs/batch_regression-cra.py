import choraconfig, glob, os.path, sys

batch = choraconfig.clone_batch("regression")

batch["toolIDs"] = ["duetcra"]
