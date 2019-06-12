import choraconfig, re, sys, os.path

def chora_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: chora_assert_results was called without a path"
        sys.exit(0)
    #e.g., "Assertion on line 13 FAILED"
    results = list()
    kind_dict = {"PASSED":"PASS","FAILED":"FAIL"}
    regex = "Assertion on line ([-0-9]+) ([A-Za-z]+)"
    with open(params["logpath"],"rb") as logfile :
        for line in logfile :
            matches = re.match(regex, line)
            if matches :
                for kind in kind_dict :
                    if kind in matches.group(2) :
                        results.append( (kind_dict[kind], int(matches.group(1))) )
                        break
                else :
                    results.append( ("UNRECOGNIZED", int(matches.group(1))) )
    return results

def chora_bounds_callout(params) :
    if "logpath" not in params : 
        print "ERROR: chora_bounds_callout was called without a path"
        sys.exit(0)
    output = ""
    with open(params["logpath"],"rb") as logfile :
        mode = 0
        for line in logfile :
            if mode == 2 :
                if line.startswith("----") or line.startswith("===="):
                    mode = 0
                else :
                    output += line
            if mode == 0 : 
                if line.startswith("---- Bounds on") or "has zero cost" in line:
                    output += line
                    #mode = 1
                    mode = 2 
                    continue
            #if mode == 1 :
            #    if line.startswith("Procedure: "):
            #        mode = 2
            #        continue
    return output

tool = choraconfig.get_default_tool_dict() 
tool["ID"] = "chora"
tool["displayname"] = "CHORA"
tool["cmd"] = [choraconfig.parent(2,choraconfig.testroot) + "/duet.native","-chora","{filename}"]
tool["bounds_callout"] = chora_bounds_callout
tool["assert_results"] = chora_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

