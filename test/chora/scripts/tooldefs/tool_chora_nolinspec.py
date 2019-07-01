import choraconfig, os.path

tool = choraconfig.clone_tool("chora")
tool["displayname"] = "CHORA:no_lin"
tool["shortname"] = "chora:no_lin"
tool["cmd"] = [choraconfig.parent(2,choraconfig.testroot) + "/duet.native","-chora-no-linspec","-chora","{filename}"]
