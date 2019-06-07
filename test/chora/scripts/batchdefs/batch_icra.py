import choraconfig, glob

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.get_tool_root("icra"),"WALi-OpenNWA/Examples/cprover/tests/")
# Small, for quick testing:
#batch["files"] = (glob.glob(batch["root"] + "c4b/*.c")[:4] + 
#                      glob.glob(batch["root"] + "sv-benchmarks/loops/*.c")[-4:])
# Too big:
#batch["files"] = [F for F in [os.path.join(R,F) for R,D,Fs in os.walk(batch["root"]) for F in Fs] if F.endswith(".c")]
icra_dirs = ["c4b", "misc-recursive", "duet", "", "STAC/polynomial/assert", 
"snlee/snlee_tests", "STAC/FiniteDifferencing", "STAC/LESE", "STAC/LowerBound", 
"STAC/LZ", "sv-benchmarks/loop-acceleration", "sv-benchmarks/loop-invgen", 
"sv-benchmarks/loop-lit", "sv-benchmarks/loop-new", "sv-benchmarks/loops", 
"sv-benchmarks/recursive", "sv-benchmarks/recursive-simple", 
"rec-sv-benchmarks/rec-loop-lit", "rec-sv-benchmarks/rec-loop-new", 
"recurrences", "exponential", "frankenstein/HOLA", "frankenstein/relational", 
"misc2017", "max_equals", "branching_loops", "strings_numeric", "ethereum"]

batch["files"] = [os.path.join(batch["root"],D,F) for D,Fs in 
           [(D, os.listdir(os.path.join(batch["root"],D))) for D in icra_dirs] # DELETE ME
        for F in Fs if F.endswith(".c")] 
batch["format_style"] = "assert"
batch["toolIDs"] = ["duetcra","icra","chora"]

