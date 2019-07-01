import choraconfig, glob, os.path

batch = choraconfig.clone_batch("icra")
#batch = choraconfig.clone_batch("assert")

batch["toolIDs"] = ["duetcra","icra","icra2019","chora_nolinspec","chora","chora_squeeze","chorafull"]
batch["timeout"] = 300

