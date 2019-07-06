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

#echo -n " CPAchecker ..."
#start=$(date +%s%N)
#echo -n "__CPA " >> $RESULT
#cd $CPA_DIR
##cd $UA_DIR
#eval "timeout $TIMEOUT $CPA -config $CPA_DIR/config/sv-comp17.properties -noout -timelimit 900 $infile.i &> $cpa_outfile"
#if (($?==124)); then
#	echo "TIMEOUT" >> $RESULT
#	echo -ne "\e[31mTimeout\e[0m"
#else
#	if grep -Pzoq "result: TRUE" $cpa_outfile; then
#		echo "PASS" >> $RESULT
#	elif grep -Pzoq "result: FALSE" $cpa_outfile; then
#		echo "FAIL" >> $RESULT
#	elif grep -Pzoq "result: UNKNOWN" $cpa_outfile; then
#		echo "UNKNOWN" >> $RESULT
#	else
#		echo "EXCEPTION" >> $RESULT
#		echo -ne "\e[31mException\e[0m"
#	fi
#fi


def cpaseq_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: cpaseq_assert_results was called without a path"
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

# really should have a tool root
tool = choraconfig.get_default_tool_dict() 
tool["displayname"] = "CPA-Seq"
tool["root"] = choraconfig.specify_tool_root_requirement("cpaseq","cpa.sh")
config_filename = "svcomp19.properties"
relative = "../config/"
troot = tool["root"]
for i in range(2) :
    cpaseq_config = os.path.realpath(os.path.join(troot,relative,config_filename))
    cpash = os.path.realpath(os.path.join(troot,"cpa.sh"))
    if os.path.exists(cpaseq_config) and os.path.exists(cpash) : break
    troot = troot.replace("\\ "," ")
else :
    print "testing.py / tool_cpaseq.py: Error trying to run CPA-Seq:"
    if not os.path.exists(cpaseq_config) :
        print "   Could not find the config file: " + config_filename
        print "   I'm looking in the directory " + relative
        print "   ... starting relative to the directory " + tool["root"] + " specified in local-test-settings.conf"
        print " File not found: " + cpaseq_config
    if not os.path.exists(cpash) :
        print "   Could not find the executable file: " + cpash
        print " File not found: " + cpash
#We used to use:
#eval "timeout $TIMEOUT $CPA -config $CPA_DIR/config/sv-comp17.properties -noout -timelimit 900 $infile.i &> $cpa_outfile"
tool["cmd"] = [os.path.join(troot,"cpa.sh"),"-config",cpaseq_config,"-noout","-timelimit","900","{preprocessed_filename}"]
tool["assert_results"] = cpaseq_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

