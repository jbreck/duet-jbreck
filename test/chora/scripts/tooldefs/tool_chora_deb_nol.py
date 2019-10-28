import choraconfig, os.path

tool = choraconfig.clone_tool("chora")
tool["displayname"] = "CHORA:deb_nol"
tool["shortname"] = "chora:deb_nol"
tool["cmd"] = [choraconfig.parent(2,choraconfig.testroot) + "/duet.native","-chora-debug-squeeze","-chora-debug-recs","-chora-no-linspec","-chora","{filename}"]
