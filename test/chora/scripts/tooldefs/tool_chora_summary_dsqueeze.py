import choraconfig, os.path

tool = choraconfig.clone_tool("chora")
tool["displayname"] = "CHORA:sds"
tool["shortname"] = "chora:sds"
tool["cmd"] = [choraconfig.parent(2,choraconfig.testroot) + "/duet.native","-chora-summaries","-chora-debug-squeeze","-chora","{filename}"]
