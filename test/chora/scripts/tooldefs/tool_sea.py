import choraconfig, re, sys, os.path, subprocess

# We used to use:
#echo -n " SEA ..."
#start=$(date +%s%N)
#echo -n "__SEA " >> $RESULT
#cd $SEA_DIR
#eval "timeout $TIMEOUT $SEA $infile.i &> $sea_outfile"
#if (($?==124)); then
#	echo "TIMEOUT" >> $RESULT
#	echo -ne "\e[31mTimeout\e[0m"
#else
#	if grep -Pzoq "Result TRUE" $sea_outfile; then
#		echo "PASS" >> $RESULT
#	elif grep -Pzoq "Result FALSE" $sea_outfile; then
#		echo "FAIL" >> $RESULT
#	elif grep -Pzoq "Result UNKNOWN" $sea_outfile; then
#		echo "UNKNOWN" >> $RESULT
#	else
#		echo "EXCEPTION" >> $RESULT
#		echo -ne "\e[31mException\e[0m"
#	fi
#fi
#end=$(date +%s%N)
#len=$(expr $end - $start)
#echo "__SEATIME $len" >> $RESULT
#
#echo -n " Done"
#echo -n " (Cleaning up SeaHorn...)"
#killall seahorn &> /dev/null
#echo ""

def sea_assert_results(params) :
    # In the past, we had problems with SeaHorn sub-processes sticking around
    #   after we had killed their parent process.  This is meant to kill off
    #   any ones that remain.
    with open(os.devnull,"w") as fnull :
        subprocess.call(["killall","seahorn"],stdout=fnull,stderr=subprocess.STDOUT)
    if "logpath" not in params : 
        print "ERROR: sea_assert_results was called without a path"
        sys.exit(0)
    results = list()
    with open(params["logpath"],"rb") as logfile : text = logfile.read()
    text = text.replace("\n"," ")
    if   re.search("result\\s+true",text,re.I) :
        results.append( ("PASS", 0) )
    elif re.search("result\\s+false",text,re.I) :
        results.append( ("FAIL", 0) )
    elif re.search("result\\s+unknown",text,re.I) :
        results.append( ("FAIL", 0) )
    else :
        results.append( ("UNRECOGNIZED", 0) )
    return results

tool = choraconfig.get_default_tool_dict() 
tool["displayname"] = "SeaHorn"
tool["root"] = choraconfig.specify_tool_root_requirement("sea","sea_svcomp")
sea_exe = os.path.join(tool["root"],"sea_svcomp")
if not os.path.exists(sea_exe) :
    print "   Could not find the executable file: " + sea_exe
    print " File not found: " + sea_exe
#We used to use:
#eval "timeout $TIMEOUT $SEA $infile.i &> $sea_outfile"
tool["cmd"] = [sea_exe,"{preprocessed_filename}"]
tool["assert_results"] = sea_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

