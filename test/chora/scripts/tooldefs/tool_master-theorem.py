import choraconfig, re, sys, os.path

def master_theorem_bounds_callout(params) :
    if "logpath" not in params : 
        print "ERROR: duet_bounds_callout was called without a path"
        sys.exit(0)
    #output = ""
    with open(params["logpath"],"rb") as logfile : output = logfile.read().strip()
    return output

# really should have a tool root
tool = choraconfig.get_default_tool_dict() 
tool["displayname"] = "Master Theorem"
tool["shortname"] = "master"
tool["root"] = choraconfig.benchroot + "rba/master-theorem"
tool["cmd"] = ["python",os.path.join(tool["root"],"mastertheorem.py"),"{filename}"]
tool["bounds_callout"] = master_theorem_bounds_callout
tool["no_assert_line_numbers"] = True
tool["error_callout"] = choraconfig.generic_error_callout


