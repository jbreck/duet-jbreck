import choraconfig, re, sys, os.path, subprocess

def viap_precheck(params) :
    prpfiles = [F for F in os.listdir(params["directory"]) if F.endswith(".prp")]
    if len(prpfiles) != 1 :
        print "testing.py / tool_viap.py : Error: could not find a unique .prp file in " + params["directory"]
        print "Maybe you want one of the ones from here: https://github.com/sosy-lab/sv-benchmarks/tree/master/c/properties"
        print "  (Jason: I'm guessing that the right one is 'unreach-call.prp')"
        sys.exit(0)
    # set "prpfile" entry in param dict for use in command construction
    params["prpfile"] = os.path.join(params["directory"],prpfiles[0])

def viap_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: viap_assert_results was called without a path"
        sys.exit(0)
    results = list()
    with open(params["logpath"],"rb") as logfile : text = logfile.read()
    text = text.replace("\n"," ")
    if   re.search("VIAP_STANDARD_OUTPUT_True",text) :
        results.append( ("PASS", 0) )
    elif re.search("VIAP_STANDARD_OUTPUT_False",text) :
        results.append( ("FAIL", 0) )
    elif re.search("Unknown",text) :
        results.append( ("FAIL", 0) )
    else :
        results.append( ("FAIL", 0) )
        #results.append( ("UNRECOGNIZED", 0) )
    return results

tool = choraconfig.get_default_tool_dict() 
tool["displayname"] = "VIAP"
tool["root"] = choraconfig.specify_tool_root_requirement("viap","viap_tool.py")
viap_exe = os.path.join(tool["root"],"viap_tool.py")
if not os.path.exists(viap_exe) :
    print "   Could not find the executable file: " + viap
    sys.exit(0)
tool["cmd"] = [viap_exe,"--spec={prpfile}","{filename}"]
tool["precheck"] = viap_precheck
tool["assert_results"] = viap_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

