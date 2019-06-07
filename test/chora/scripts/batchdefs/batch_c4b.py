import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

batch["ID"] = "c4b"
batch["root"] = os.path.join(choraconfig.get_tool_root("icra"),"/WALi-OpenNWA/Examples/cprover/tests/")
batch["files"] = glob.glob(c4b["root"] + "c4b/*.c")
batch["format_style"] = "assert"


