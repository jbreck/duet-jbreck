import choraconfig, re, sys, os.path

def duet_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: duet_assert_results was called without a path"
        sys.exit(0)
    if "tmpfile" not in params : 
        print "ERROR: duet_assert_results was called without a tmpfile"
        sys.exit(0)
    results = list()
    regex = "(PASS|FAIL)"
    with open(params["tmpfile"],"rb") as tmpfile :
        for line in tmpfile :
            for result in re.findall(regex, line) :
                results.append( (result, 0) )
                break
    return results

def duet_bounds_callout(params) :
    if "logpath" not in params : 
        print "ERROR: duet_bounds_callout was called without a path"
        sys.exit(0)
    output = ""
    with open(params["logpath"],"rb") as logfile :
        mode = 0
        for line in logfile :
            if mode == 0 : 
                if line.startswith("Procedure:"):
                    output += line
                    mode = 2 
                    continue
            if mode == 2 :
                #if line.startswith("==========="):
                #    mode = 0
                #    continue
                output += line
    return output

# really should have a tool root
tool = choraconfig.get_default_tool_dict() 
tool["ID"] = "duetcra"
tool["displayname"] = "CRA"
tool["shortname"] = "cra"
tool["root"] = choraconfig.specify_tool_root_requirement("duetcra","duet.native")
tool["cmd"] = [os.path.join(tool["root"],"duet.native"),"-cra","{filename}","-test","{tmpfile}"]
tool["bounds_callout"] = duet_bounds_callout
tool["assert_results"] = duet_assert_results
tool["no_assert_line_numbers"] = True
tool["error_callout"] = choraconfig.generic_error_callout


