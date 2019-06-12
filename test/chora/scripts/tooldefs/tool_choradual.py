import choraconfig, os.path

tool = choraconfig.clone_tool("chora")
tool["displayname"] = "CHORA:dual"
tool["shortname"] = "chora:dual"
tool["cmd"] = [choraconfig.parent(2,choraconfig.testroot) + "/duet.native","-chora-dual","-chora","{filename}"]
