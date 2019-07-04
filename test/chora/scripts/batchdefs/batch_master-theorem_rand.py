import choraconfig, glob, os.path, random

batch = choraconfig.get_default_batch_dict()

batch["root"] = choraconfig.benchroot + "rba/master-theorem"
#batch["files"] = list()
case1 = list()
case2 = list()
case3 = list()
progs = list()
for adir, dirs, files in os.walk(batch["root"]) :
    if "backups" in adir or "template" in adir : continue
    print adir
    if "case1" in adir:
        case1 += glob.glob(adir+"/*.c")
    elif "case2" in adir:
        case2 += glob.glob(adir+"/*.c")
    else:
        case3 += glob.glob(adir+"/*.c")
    #batch["files"] += glob.glob(adir + "/*.c")
    progs += glob.glob(adir + "/*.c")
num_case1 = 5
num_case2 = 5
num_case3 = 5
random.shuffle(case1)
random.shuffle(case2)
random.shuffle(case3)
batch["files"] = case1[:num_case1] + case2[:num_case2] + case3[:num_case3]
batch["format_style"] = "rba"
batch["warmupfiles"] = ["rba/cost_fib.c","rba/cost_fib_eq.c"]
batch["toolIDs"] = ["chora_summary_dsqueeze","master-theorem"]
#batch["format_col_width_proportional"] = True
batch["timeout"] = 60

