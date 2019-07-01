import choraconfig, os.path

tool = choraconfig.clone_tool("chora")
tool["displayname"] = "CHORA:squeeze"
tool["shortname"] = "chora:squeeze"
tool["cmd"] = [choraconfig.parent(2,choraconfig.testroot) + "/duet.native","-chora-squeeze","-chora","{filename}"]
