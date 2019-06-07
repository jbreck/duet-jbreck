import choraconfig, re, sys, os.path

def icra_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: icra_assert_results was called without a path"
        sys.exit(0)
    #e.g., "Assertion on line 13 FAILED"
    results = list()
    kind_dict = {"PASSED":"PASS","FAILED":"FAIL"}
    regex = "Assertion on line ([-0-9]+) ([A-Za-z]+)"
    with open(params["logpath"],"rb") as logfile :
        for line in logfile :
            matches = re.search(regex, line)
            if matches :
                for kind in kind_dict :
                    if kind in matches.group(2) :
                        results.append( (kind_dict[kind], int(matches.group(1))) )
                        break
                else :
                    results.append( ("UNRECOGNIZED", int(matches.group(1))) )
    return results

def icra_bounds_callout(params) :
    if "logpath" not in params : 
        print "ERROR: icra_bounds_callout was called without a path"
        sys.exit(0)
    output = ""
    with open(params["logpath"],"rb") as logfile :
        mode = 0
        for line in logfile :
            if mode == 0 : 
                if line.startswith("Bounds on Variables"):
                    output += line
                    mode = 1
                    continue
            if mode == 1 : # skip a line
                mode = 2 
                continue
            if mode == 2 :
                if line.startswith("==========="):
                    mode = 0
                    continue
                output += line
    return output

# really should have a tool root
tool = choraconfig.get_default_tool_dict() 
tool["ID"] = "icra"
tool["displayname"] = "ICRA"
tool["root"] = choraconfig.specify_tool_root_requirement("icra","icra")
tool["cmd"] = [os.path.join(tool["root"],"icra"),"{filename}"]
tool["bounds_callout"] = icra_bounds_callout
tool["assert_results"] = icra_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

