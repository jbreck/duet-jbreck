import choraconfig, re, sys, os.path

# We used to use:
#echo -n " UAutomizer ..."
#start=$(date +%s%N)
#echo -n "__UA " >> $RESULT
#cd $UA_DIR
#eval "timeout $TIMEOUT $UA --full-output $directory/ALL.prp 64bit precise $infile.i &> $ua_outfile"
#if (($?==124)); then
#	echo "TIMEOUT" >> $RESULT
#	echo -ne "\e[31mTimeout\e[0m"
#else
#	if grep -Pzoq "Result:\nTRUE" $ua_outfile; then
#		echo "PASS" >> $RESULT
#	elif grep -Pzoq "Result:\nFALSE" $ua_outfile; then
#		echo "FAIL" >> $RESULT
#	elif grep -Pzoq "Result:\nUNKNOWN" $ua_outfile; then
#		echo "UNKNOWN" >> $RESULT
#	else
#		echo "EXCEPTION" >> $RESULT
#		echo -ne "\e[31mException\e[0m"
#	fi
#fi
#end=$(date +%s%N)
#len=$(expr $end - $start)
#echo "__UATIME $len" >> $RESULT

def ua_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: ua_assert_results was called without a path"
        sys.exit(0)
    results = list()
    with open(params["logpath"],"rb") as logfile : text = logfile.read()
    text = text.replace("\n"," ")
    if   re.search("result:\\s+true",text,re.I) :
        results.append( ("PASS", 0) )
    elif re.search("result:\\s+false",text,re.I) :
        results.append( ("FAIL", 0) )
    elif re.search("result:\\s+unknown",text,re.I) :
        results.append( ("FAIL", 0) )
    else :
        results.append( ("UNRECOGNIZED", 0) )
    return results

def ua_precheck(params) :
    prpfiles = [F for F in os.listdir(params["directory"]) if F.endswith(".prp")]
    if len(prpfiles) != 1 :
        print "testing.py / tool_ua.py : Error: could not find a unique .prp file in " + params["directory"]
        print "Maybe you want one of the ones from here: https://github.com/sosy-lab/sv-benchmarks/tree/master/c/properties"
        print "  (Jason: I'm guessing that the right one is 'unreach-call.prp')"
        sys.exit(0)
    # set "prpfile" entry in param dict for use in command construction
    params["prpfile"] = os.path.join(params["directory"],prpfiles[0])

# really should have a tool root
tool = choraconfig.get_default_tool_dict() 
tool["displayname"] = "U. Automizer"
tool["root"] = choraconfig.specify_tool_root_requirement("ua","Ultimate.py")
uapy = os.path.join(tool["root"],"Ultimate.py")
if not os.path.exists(uapy) :
    print "   Could not find the executable file: " + uapy
    print " File not found: " + uapy
#We used to use:
# eval "timeout $TIMEOUT $UA --full-output $directory/ALL.prp 64bit precise $infile.i &> $ua_outfile"
#Note that "{prpfile}" is set by the pre-check function
tool["cmd"] = [uapy,"--full-output","--spec","{prpfile}","--architecture","64bit","--file","{preprocessed_filename}"]
tool["precheck"] = ua_precheck
tool["assert_results"] = ua_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

