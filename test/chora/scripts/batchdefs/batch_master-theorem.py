import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

batch["root"] = choraconfig.benchroot + "rba/master-theorem"
batch["files"] = list()
for adir, dirs, files in os.walk(batch["root"]) :
    if "backups" in adir or "template" in adir : continue
    print adir
    batch["files"] += glob.glob(adir + "/*.c")
batch["format_style"] = "rba"
batch["warmupfiles"] = ["rba/cost_fib.c","rba/cost_fib_eq.c"]
batch["toolIDs"] = ["chora_summary_dsqueeze","master-theorem"]
#batch["format_col_width_proportional"] = True
batch["timeout"] = 60

