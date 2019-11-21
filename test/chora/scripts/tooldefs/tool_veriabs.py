import choraconfig, re, sys, os.path

def veriabs_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: veriabs_assert_results was called without a path"
        sys.exit(0)
    results = list()
    with open(params["logpath"],"rb") as logfile : text = logfile.read()
    text = text.replace("\n"," ")
    if   re.search("VERIABS_VERIFICATION_SUCCESSFUL",text) :
        results.append( ("PASS", 0) )
    elif re.search("RIABS_VERIFICATION_FAILED",text) :
        results.append( ("FAIL", 0) )
    else :
        results.append( ("FAIL", 0) )
    # Sometimes"VERIABS_UNKNOWN" is given
    #
    #elif re.search("result:\\s+unknown",text,re.I) :
    #    results.append( ("FAIL", 0) )
    #else :
    #    results.append( ("UNRECOGNIZED", 0) )
    return results

def veriabs_precheck(params) :
    prpfiles = [F for F in os.listdir(params["directory"]) if F.endswith(".prp")]
    if len(prpfiles) != 1 :
        print "testing.py / tool_utaipan.py : Error: could not find a unique .prp file in " + params["directory"]
        print "Maybe you want one of the ones from here: https://github.com/sosy-lab/sv-benchmarks/tree/master/c/properties"
        print "  (Jason: I'm guessing that the right one is 'unreach-call.prp')"
        sys.exit(0)
    # set "prpfile" entry in param dict for use in command construction
    params["prpfile"] = os.path.join(params["directory"],prpfiles[0])

# really should have a tool root
tool = choraconfig.get_default_tool_dict() 
tool["displayname"] = "VeriAbs"
tool["root"] = choraconfig.specify_tool_root_requirement("veriabs","scripts/veriabs")
veriabs_exe = os.path.join(tool["root"],"scripts","veriabs")
if not os.path.exists(veriabs_exe) :
    print "   Could not find the executable file: " + veriabs_exe
    print " File not found: " + veriabs_exe
    sys.exit(0)
tool["cmd"] = [veriabs_exe,"--property-file","{prpfile}","{filename}"]
tool["precheck"] = veriabs_precheck
tool["assert_results"] = veriabs_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

