import choraconfig, glob, os.path, sys

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.benchroot,"icrasuite/")

icra_dirs = ["c4b", "misc-recursive", "duet", "", "STAC/polynomial/assert", 
"snlee/snlee_tests", "STAC/FiniteDifferencing", "STAC/LESE", "STAC/LowerBound", 
"STAC/LZ", "sv-benchmarks/loop-acceleration", "sv-benchmarks/loop-invgen", 
"sv-benchmarks/loop-lit", "sv-benchmarks/loop-new", "sv-benchmarks/loops", 
"sv-benchmarks/recursive", "sv-benchmarks/recursive-simple", 
"rec-sv-benchmarks/rec-loop-lit", "rec-sv-benchmarks/rec-loop-new", 
"recurrences", "exponential", "frankenstein/HOLA", "frankenstein/relational", 
"misc2017", "max_equals", "branching_loops", "strings_numeric", "ethereum"]

blacklist = list()

# Mutual recursion
blacklist.extend([
 "t39.c",
 "EvenOdd01_true-unreach-call_true-termination.c",
 "EvenOdd03_false-unreach-call_false-termination.c",
 "afterrec_2calls_false-unreach-call.c",
 "afterrec_2calls_true-unreach-call.c",
 "fibo_2calls_10_false-unreach-call.c",
 "fibo_2calls_10_true-unreach-call.c",
 "fibo_2calls_15_false-unreach-call.c",
 "fibo_2calls_15_true-unreach-call.c",
 "fibo_2calls_20_false-unreach-call.c",
 "fibo_2calls_20_true-unreach-call.c",
 "fibo_2calls_25_false-unreach-call.c",
 "fibo_2calls_25_true-unreach-call.c",
 "fibo_2calls_2_false-unreach-call.c",
 "fibo_2calls_2_true-unreach-call.c",
 "fibo_2calls_4_false-unreach-call.c",
 "fibo_2calls_4_true-unreach-call.c",
 "fibo_2calls_5_false-unreach-call.c",
 "fibo_2calls_5_true-unreach-call.c",
 "fibo_2calls_6_false-unreach-call.c",
 "fibo_2calls_6_true-unreach-call.c",
 "fibo_2calls_8_false-unreach-call.c",
 "fibo_2calls_8_true-unreach-call.c",
 "id2_b2_o3_true-unreach-call.c",
 "id2_b3_o2_false-unreach-call.c",
 "id2_b3_o5_true-unreach-call.c",
 "id2_b5_o10_true-unreach-call.c",
 "id2_i5_o5_false-unreach-call.c",
 "id2_i5_o5_true-unreach-call.c",
])

# Misc errors that are not tool regressions
blacklist.extend([
 "AGHKTW2017_loopAndBranch_unsafe.c",
 "log_log_n_solution.c",
 "log_log_n_solution_unsafe.c",
 "two_to_n_squared.c",
 "two_to_n_squared_unsafe.c",
])

# Uninteresting timeouts
blacklist.extend([
 "lz77.c",
])
  
batch["files"] = [os.path.join(batch["root"],D,F) for D,Fs in 
           [(D, os.listdir(os.path.join(batch["root"],D))) for D in icra_dirs]
        for F in Fs if F.endswith(".c") and os.path.basename(F) not in blacklist] 

batch["format_style"] = "assert"
batch["toolIDs"] = ["chora"]

batch["timeout"] = 30 # short timeout for quick testing

batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
batch["hide_default_exits"] = True
