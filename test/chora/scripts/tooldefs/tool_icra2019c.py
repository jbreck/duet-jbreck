import choraconfig, re, sys, os.path

tool = choraconfig.clone_tool("icra")
tool["root"] = choraconfig.specify_tool_root_requirement("icra2019","icra")
tool["displayname"] = "ICRA:2019c"
tool["shortname"] = "icra:2019c"
tool["cmd"] = [os.path.join(tool["root"],"icra"),"--bound-entry","__cost","{filename}","-newton-verbosity","0"]
