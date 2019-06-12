import choraconfig, glob

batch = choraconfig.get_default_batch_dict()

batch["files"] = glob.glob(choraconfig.benchroot + "rba/*.c")
batch["format_style"] = "rba"
batch["warmupfiles"] = ["rba/cost_fib.c","rba/cost_fib_eq.c"]
batch["toolIDs"] = ["chora","choradual","chorafull"]
#batch["format_col_width_proportional"] = True
batch["timeout"] = 60

