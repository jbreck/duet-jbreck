#!/usr/bin/python
import os.path, sys, glob, datetime, time, subprocess, shutil, re
import xml.sax.saxutils, csv, tempfile
import choraconfig

def usage() :
    print "USAGE: testing.py --run <batchname>"
    print "         to start a new testing run"
    print "   OR  testing.py --format <run_id>"
    print "         to reformat the results of the previous testing run with ID <run_id>"
    print ""
    print "   To define your own batches of tests, or analysis tools,"
    print "     create or modify the files in batchdefs/batch_*.py or"
    print "     tooldefs/tool_*.py."
    sys.exit(0)

def yes_post_slash(d) :
    if d[-1] == "/" : return d
    return d + "/"

# TODO: allow for timing of multiple trials
class Datfile :
    def __init__(self, datpath) :
        self.data = dict()
        with open(datpath,"rb") as dat :
            csvreader = csv.reader(dat, delimiter="\t")
            for row in csvreader :
                if len(row) == 0 : continue
                cellpairs = [C.split("=",1) for C in row if "=" in C]
                cells = {P[0]:P[1] for P in cellpairs}
                if "source" not in cells :
                    print "WARNING: Unrecognized datfile line: " + line
                    continue
                if "tool" not in cells :
                    print "WARNING: Unrecognized datfile line: " + line
                    continue
                if cells["source"] not in self.data : 
                    self.data[cells["source"]] = dict()
                if cells["tool"] in self.data[cells["source"]] :
                    print "WARNING: duplicating source/tool combination in datfile: " + line
                self.data[cells["source"]][cells["tool"]] = cells
    def get_default(self, source, tool, key, default) :
        if source not in self.data : return default
        if tool not in self.data[source] : return default
        if key not in self.data[source][tool] : return default
        return self.data[source][tool][key]

def detect_safe_benchmark(path) :
    # return "safe" or "unsafe" or "mixed"
    basename = os.path.basename(path)
    if (('unsafe' in basename) or ('false-unreach-call' in basename)) :
        return "unsafe"
    return "safe"

def reformat_float_string(s,form) :
    try :
        return form % float(s)
    except :
        return s

def format_conclusion(conclusion, is_safe) :
    if (conclusion == "ERROR") :
        return '<b><font color=\"#600060\">ERROR</font></b><br>'
    if (conclusion == "TIMEOUT") :
        return '<font color=\"#800080\">TIMEOUT</font><br>'
    if (conclusion == "MEMOUT") :
        return '<font color=\"#900020\">MEMOUT</font><br>'
    if (conclusion == "N/A") :
        return '<font color=\"#000000\">N/A</font><br>'
    if is_safe == "safe" :
        if (conclusion == "PASS"):
            return '<font color=\"#00AA00\">PASS</font>'
        elif (conclusion == "FAIL"):
            return '<font color=\"#FF0000\">FAIL</font>'
    elif is_safe == "unsafe" :
        if (conclusion == "PASS"):
            return '<b><font color=\"#FF0000\">UNSOUND</font></b>'
        elif (conclusion == "FAIL"):
            return '<font color=\"#00AA00\">OKAY</font>'
    else :
        return '<font color=\"#000000\">MIXED</font>'
    return '<font color=\"#FF00DF\">?'+conclusion+'?</font>'

def aggregate_assert_results(assert_str, exitType, is_safe, style, error_str) :
    # assert_str looks something like "[PASS@11;FAIL@17;PASS@19]"
    # exitType is "default" or "timeout" or "error" or "memout"
    #   maybe add "unknown" later?
    # should do this all through pluggable formatter
    out = dict()
    if len(assert_str) >= 2 :
        assert_parts = assert_str[1:-1].split(";")
    else :
        assert_parts = [""]
    out["safe_good"] = 0
    out["unsafe_good"] = 0
    if exitType == "timeout" :
        out["conclusion"] = "TIMEOUT"
    elif exitType == "memout" :
        out["conclusion"] = "MEMOUT"
    elif exitType == "error" :
        out["conclusion"] = "ERROR"
    elif exitType == "default" :
        if len(assert_parts) == 0 or assert_parts == [""] :
            out["conclusion"] = "N/A"
        elif is_safe == "safe" :
            if all(P.startswith("PASS") for P in assert_parts) :
                out["conclusion"] = "PASS"
                out["safe_good"] = 1
            else :
                out["conclusion"] = "FAIL"
        elif is_safe == "unsafe" :
            if all(P.startswith("FAIL") for P in assert_parts) :
                out["conclusion"] = "FAIL"
                out["unsafe_good"] = 1
            else :
                out["conclusion"] = "PASS"
                out["unsound"] = True
        else :
            out["conclusion"] = "MIXED"
    else :
        out["conclusion"] = "UNKNOWN"
    conclusion_html = ("<span title='"+ 
                       "exitType="+exitType+",  asserts="+assert_str+error_str+"'>"+
                       format_conclusion(out["conclusion"],is_safe)+
                       "</span>")
    if style == "short" :
        out["html"] = conclusion_html
    else :
        if len(assert_parts) > 1 :
            out["html"] = ("<br>".join(assert_parts)+"<br>="+
                          conclusion_html)

        else :
            out["html"] = conclusion_html
    return out

def check_formatting_flag(flag, formatting) :
    return flag in formatting and bool(formatting[flag]) == True

class HTMLTable :
    def __init__(self) :
        self.columns = list()
        self.rows = list()
        self.data = dict()
        self.style = "border='1px'" 
        self.prefix = ""
        self.column_weights = dict()
        self.flags = list()
    def register_row(self,rowid) :
        if rowid not in self.rows : self.rows.append(rowid)
    def register_column(self,colid) :
        if colid not in self.columns : self.columns.append(colid)
        if colid not in self.column_weights : self.column_weights[colid] = 1.0
    def set_column_weight(self,colid,weight) :
        self.column_weights[colid] = weight
    def set_prefix(self, prefix) : self.prefix = prefix
    def set_flag(self, flag) : 
        if not flag in self.flags : self.flags.append(flag)
    def flag(self, flag) : return flag in self.flags
    def new_row(self) : 
        rowid = "row"+str(len(self.rows))
        self.register_row(rowid)
        return rowid
    def set(self,rowid,colid,text) :
        #if rowid is None : rowid = self.new_row()
        self.register_row(rowid)
        self.register_column(colid)
        if rowid not in self.data : self.data[rowid] = dict()
        self.data[rowid][colid] = text
        return (rowid,colid)
    def get(self,rowid,colid) :
        #if rowid is None : 
        #    if len(self.rows) > 0 : rowid = self.rows[-1]
        #    else : rowid = self.new_row()
        self.register_row(rowid)
        self.register_column(colid)
        if rowid not in self.data : self.data[rowid] = dict()
        if colid not in self.data[rowid] : self.data[rowid][colid] = ""
        return self.data[rowid][colid]
    def show(self, formatting) :
        if check_formatting_flag("col_width_proportional",formatting) : 
            self.style += " style='width:100%;table-layout:fixed;' "
        output = "<table " + self.style + " >\n"
        output += self.prefix
        if check_formatting_flag("col_width_proportional",formatting) : 
            if not "colgroup" in self.prefix :
                total_weight = sum([self.column_weights[C] for C in self.columns])
                pct = dict()
                for col in reversed(self.columns[1:]) :
                    pct[col] = int(100 * self.column_weights[col] / total_weight)
                if len(self.columns) > 0 : pct[self.columns[0]] = 100 - sum(pct[C] for C in pct)
                for col in self.columns :
                    output += """<col span="1" style="width:%d%%;">""" % pct[col]
                output += """\n"""
        rows = self.rows
        columns = self.columns
        bgIndex = 0
        for row in rows :
            styling = ""
            if check_formatting_flag("alternate_bgcolor",formatting) : 
                styling = 'style="background-color:'+["white","#CCCCCC"][bgIndex]+';"'
                bgIndex = 1 - bgIndex
            output += "<tr "+styling+">"
            for col in columns :
                output += "<td>" + self.get(row,col) + "</td>"
            output += "</tr>\n"
        output += "</table>\n"
        return output

def sort_dir_major(f) : return ( os.path.dirname(f), os.path.basename(f) )

def run(batch, stamp) :
    tools = [choraconfig.get_tool_by_ID(I) for I in batch.get("toolIDs")]
    print "RUN ID=" + stamp
    outroot = choraconfig.testroot + "/output"
    outrun = outroot + "/" + stamp
    runlogpath = outrun + "/run.dat"
    donefile = outrun + "/run_complete.txt"
    outsources = outrun + "/sources/"
    choraconfig.makedirs(outsources)
    formatting = []
    formatting.append("format_batchID="+batch.get("ID"))
    formatting.append("format_toolIDs="+",".join(batch.get("toolIDs")))
    for key in batch.d :
        if key.startswith("format_") :
            formatting.append(key+"="+str(batch.d[key]))
    formattingpath = outrun + "/formatdata.txt"
    with open(formattingpath, "wb") as formatfile :
        for line in formatting :
            print >>formatfile, line
    if not batch.hasattr("root"):
        print "ERROR: batch['root'] was not specified"
        return
    for filename in sorted(batch.get("files")) :
        if not filename.startswith(batch.get("root")) :
            print "ERROR: not all files in batch are under the batch['root']"
            print "   batch['root']="+str(batch.get("root"))
            print "   exceptional filename = "+str(filename)
            return
    if batch.hasattr("warmupfiles") and len(batch.get("warmupfiles")) > 0 :
        print ""
        print "  Warmup..."
        with open(os.devnull, 'w') as devnull:
            for tool in tools : 
                for filename in batch.get("warmupfiles") :
                    cmd = [S.format(filename=filename) for S in tool.get("cmd")]
                    subprocess.call(cmd, stdout=devnull, stderr=devnull)
    print ""
    with open(runlogpath,"wb") as runlog :
        for filename in sorted(batch.get("files"), key=sort_dir_major) :
            nicename = filename
            br_prefix = yes_post_slash(batch.get("root"))
            if nicename.startswith(br_prefix) : nicename = nicename[len(br_prefix):]
            sys.stdout.write(" " + nicename + " ")
            sourcedest = outsources + nicename
            choraconfig.makedirs(os.path.dirname(sourcedest))
            shutil.copyfile(filename, sourcedest)
            anyProblem = False
            for tool in tools : 
                handle, tmpfile = tempfile.mkstemp(suffix="choratmpfile.txt")
                os.close(handle)
                cmd = [S.format(filename=filename, tmpfile = tmpfile) for S in tool.get("cmd")]
                logpath = outrun + "/logs/" + nicename + "." + tool.ID + ".log"
                choraconfig.makedirs(os.path.dirname(logpath))
                startTime = time.time()
                exitType = "unknown"
                sys.stdout.write("["+tool.ID+":")
                sys.stdout.flush()
                timeTaken = -1.0
                with open(logpath,"w") as logfile :
                    print >>logfile, " ".join(cmd)
                    print >>logfile, ""
                    logfile.flush()
                    child = subprocess.Popen(cmd, stdout=logfile, stderr=subprocess.STDOUT)
                    while True :
                        timeTaken = time.time() - startTime
                        if child.poll() is not None :
                            if (child.returncode != 0 and
                               not tool.flag("nonzero_error_code_is_benign")) :
                                exitType = "error"
                                sys.stdout.write(choraconfig.color_start+
                                                 "ERROR"+
                                                 choraconfig.color_stop+"] ")
                                sys.stdout.flush()
                                anyProblem = True
                                break
                            exitType = "default"
                            sys.stdout.write("OK] ")
                            sys.stdout.flush()
                            break
                        if timeTaken >= batch.get("timeout") :
                            child.kill()
                            exitType = "timeout"
                            sys.stdout.write("T/O] ")
                            sys.stdout.flush()
                            anyProblem = True
                            break
                runlogline = ""
                runlogline += "source="+nicename+"\t"
                runlogline += "tool="+tool.ID+"\t"
                runlogline += "exit="+exitType+"\t"
                runlogline += "time="+str(timeTaken)+"\t"
                #trialNo = 0
                #runlogline += "trial="+trialNo+"\t" # maybe?
                if tool.hasattr("assert_results") :
                    results = tool.get("assert_results")({"logpath":logpath,"tmpfile":tmpfile})
                    if tool.flag("no_assert_line_numbers") : 
                        result_str = ";".join(R[0]+"@?" for R in results)
                    else : 
                        results = sorted(results,key=lambda R:R[1])
                        result_str = ";".join(R[0]+"@"+str(R[1]) for R in results)
                    runlogline += "assert=["+result_str+"]\t"
                    if batch.flag("instant_unsound_callouts") :
                        is_safe = detect_safe_benchmark(filename)
                        if is_safe == "unsafe" and any(R[0].startswith("PASS") for R in results) :
                            sys.stdout.write("\n   Warning: "+choraconfig.color_start+
                                    "UNSOUND"+choraconfig.color_stop+" result!\n")
                            sys.stdout.write("  ")
                            sys.stdout.flush()
                            anyProblem = True
                runlogline += "runid="+stamp+"\t"
                while len(runlogline) > 0 and runlogline[-1]=="\t" : runlogline = runlogline[:-1]
                print >>runlog, runlogline
                if (exitType == "error" and tool.hasattr("error_callout") 
                    and batch.flag("instant_error_callouts")) :
                    error_raw = tool.get("error_callout")({"logpath":logpath})
                    if len(error_raw.strip()) > 0 :
                        sys.stdout.write("\n   Possible error-related text in logfile follows:\n")
                        for line in error_raw.split("\n") :
                            sys.stdout.write("     " + line.rstrip() + "\n")
                        sys.stdout.write("  ")
                        sys.stdout.flush()
                os.remove(tmpfile)
            if batch.flag("hide_default_exits") and not anyProblem :
                sys.stdout.write("\r" + " "*115 + "\r")
                sys.stdout.flush()
            else :
                sys.stdout.write("\n")
                sys.stdout.flush()

    newstamp = datetime.datetime.now().strftime("%Y/%m/%d at %H:%M:%S")
    print ""
    completion = "Run ID=" + stamp + " completed at " + newstamp
    print completion
    with open(donefile,"wb") as done : print >>done, completion

    format_run(outrun)

created_html_files = list()

def format_run(outrun) :
    if not os.path.isdir(outrun) : 
        outrun = choraconfig.testroot + "/output/" + outrun
    if not os.path.isdir(outrun) : 
        print "Wasn't a directory: " + outrun
        usage()
    formatting = dict()
    formattingpath = outrun + "/formatdata.txt"
    with open(formattingpath, "rb") as formatfile :
        for line in formatfile :
            if "=" not in line : continue
            line = line.rstrip()
            parts = line.split("=",1)
            fk = "format_"
            if parts[0].startswith(fk) : parts[0]=parts[0][len(fk):]
            formatting[parts[0]]=parts[1]
    if formatting["style"] == "rba" :
        htmlpath = outrun+"/rba.html"
        created_html_files.append(htmlpath)
    elif formatting["style"] == "assert" :
        htmlpath = outrun+"/assert.html"
        created_html_files.append(htmlpath)
    else :
        print "Unrecognized formatting style requested: " + formatting["style"]
    if formatting["style"] in ["rba","assert"] :
        with open(htmlpath,"wb") as html :
            print >>html, "<html>\n<body>"

            datfile = Datfile(outrun+"/run.dat")

            sourcefiles = list()
            sourceroot = outrun+"/sources/"
            for curdir, dirs, files in os.walk(sourceroot):
                localsourcefiles = list()
                for filename in files :
                    path = os.path.join(curdir,filename)
                    if not path.endswith(".c") : continue
                    nicepath = path[len(sourceroot):]
                    localsourcefiles.append(nicepath)
                sourcefiles.extend(localsourcefiles)
            sourcefiles = sorted(sourcefiles, key=sort_dir_major)

            logroot = outrun+"/logs/"
            #logtoolIDs = list()
            #toolre = re.compile(".*[.](.*)[.]log$")
            #for curdir, dirs, files in os.walk(logroot):
            #    for filename in files :
            #        if not filename.endswith(".log") : continue
            #        matches = toolre.match(filename)
            #        if matches :
            #            logtoolIDs.append(matches.group(1))
            #logtoolIDs = sorted(set(logtoolIDs))
            format_toolIDs = formatting["toolIDs"].split(",")
            tools = list()
            for toolID in format_toolIDs :
                tools.append(choraconfig.get_tool_by_ID(toolID))
                #if toolID in alltools :
                #    tools.append(alltools[toolID])
                #else :
                #    print "WARNING: unrecognized tool ID: " + toolID
                #    print "         Creating a default tool with that name."
                #    tools.append(Tool({"ID":toolID}))

            table = HTMLTable()
            #table.prefix = """<colgroup> <col span="1" style="width:600px;"> </colgroup>\n"""
            if formatting["style"] == "rba" :
                # register rows and columns
                table.register_row("head")
                for sourcefile in sourcefiles : table.register_row("src/"+sourcefile)
                table.register_column("benchmark")
                table.register_column("logs")
                for tool in tools : 
                    table.register_column("tooltime/"+tool.ID)
                    table.register_column("toolrba/"+tool.ID)
                table.set_column_weight("benchmark",3.0)
                for tool in tools : 
                    table.set_column_weight("tooltime/"+tool.ID,1.0)
                    table.set_column_weight("toolrba/"+tool.ID,4.0)

                # fill in table
                table.set("head","benchmark","Benchmark")
                table.set("head","logs","Full<br>Logs")
                for tool in tools :
                    table.set("head","tooltime/"+tool.ID, tool.get("displayname") + "<br>Time (s)")
                    table.set("head","toolrba/"+tool.ID, tool.get("displayname") + "<br>Resource Bounds")
                for sourcefile in sourcefiles :
                    sourcefilekey = "src/"+sourcefile
                    table.set(sourcefilekey,"benchmark","<a href='sources/"+sourcefile+"'>"+sourcefile+"</a>")
                    loglinks = list()
                    for tool in tools :
                        timestring = reformat_float_string(datfile.get_default(sourcefile,tool.ID,"time",""),"%0.3f")
                        table.set(sourcefilekey,"tooltime/"+tool.ID,timestring)
                        logrel = sourcefile + "." + tool.ID + ".log"
                        logpath = logroot + logrel
                        if not os.path.exists(logpath) : continue
                        loglinks.append("<a href='logs/" + logrel + "'>[" + tool.ID + "]</a>")
                        if tool.hasattr("bounds_callout") : 
                            bc_result = ("<pre style='white-space:pre-wrap;'>"
                                        +xml.sax.saxutils.escape(
                                          tool.get("bounds_callout")
                                                  ({"logpath":logpath}))
                                        +"</pre>")
                        else :
                            bc_result = 'No "bounds_callout" for this tool'
                        table.set(sourcefilekey,
                                  "toolrba/"+tool.ID,
                                  bc_result)
                    table.set(sourcefilekey,"logs"," ".join(loglinks))
                print >>html, table.show(formatting)
                print >>html, "</body></html>"
                print "HTML output available at: " + htmlpath
            elif formatting["style"] == "assert" :
                # register rows and columns
                table.register_row("head")
                for sourcefile in sourcefiles : table.register_row("src/"+sourcefile)
                table.register_column("benchmark")
                table.register_column("logs")
                for tool in tools : 
                    table.register_column("tooltime/"+tool.ID)
                    table.register_column("toolassert/"+tool.ID)
                table.set_column_weight("benchmark",4.0)
                for tool in tools : 
                    table.set_column_weight("tooltime/"+tool.ID,1.0)
                    table.set_column_weight("toolassert/"+tool.ID,1.0)

                # fill in table
                table.set("head","benchmark","Benchmark")
                table.set("head","logs","Full<br>Logs")
                for tool in tools :
                    table.set("head","tooltime/"+tool.ID, tool.get("displayname") + "<br>Time (s)")
                    table.set("head","toolassert/"+tool.ID, tool.get("displayname") + "<br>Assertions")
                for sourcefile in sourcefiles :
                    sourcefilekey = "src/"+sourcefile
                    table.set(sourcefilekey,"benchmark","<a href='sources/"+sourcefile+"'>"+sourcefile+"</a>")
                    loglinks = list()
                    for tool in tools :
                        timestring = reformat_float_string(datfile.get_default(sourcefile,tool.ID,"time",""),"%0.3f")
                        table.set(sourcefilekey,"tooltime/"+tool.ID,timestring)
                        logrel = sourcefile + "." + tool.ID + ".log"
                        logpath = logroot + logrel
                       
                        assert_str = datfile.get_default(sourcefile,tool.ID,"assert","")
                        exitType = datfile.get_default(sourcefile,tool.ID,"exit","")
                        is_safe = detect_safe_benchmark(sourcefile)
                        error_str = ""
                        if exitType == "error" and tool.hasattr("error_callout"):
                            error_raw = tool.get("error_callout")({"logpath":logpath})
                            if len(error_raw.strip()) > 0 :
                                error_str = ("\nPossible error-related text in logfile follows:\n"+
                                             xml.sax.saxutils.escape(error_raw).replace("'","\""))

                        assert_out = aggregate_assert_results(assert_str, exitType, is_safe, "short", error_str)

                        table.set(sourcefilekey, "toolassert/"+tool.ID, assert_out["html"])

                        if not os.path.exists(logpath) : continue
                        loglinks.append("<a href='logs/" + logrel + "'>[" + tool.get("shortname") + "]</a>")
                    table.set(sourcefilekey,"logs"," ".join(loglinks))
                print >>html, table.show(formatting)
                print >>html, "</body></html>"
                print "HTML output available at: " + htmlpath
            else :
                print "Unrecognized formatting style: " + formatting["style"] 

if __name__ == "__main__" :
    # obviously, I should use a real command-line processing system here
    if len(sys.argv) < 3 :
        if "--run" in sys.argv :
            choraconfig.print_known_batches()
        usage()
    if sys.argv[1] == "--run" : 
        batchid = sys.argv[2]
        stamp = datetime.datetime.now().strftime("%Y_%m_%d_at_%H_%M_%S") + "_" + batchid
        for arg in sys.argv :
            matches = re.match("--stamp=(.*)",arg)
            if matches :
                stamp = matches.group(1)
        run(choraconfig.get_batch_by_ID(batchid),stamp)
    elif sys.argv[1] == "--format" :
        if len(sys.argv) < 2 : usage()
        outrun = sys.argv[2]
        format_run(outrun)
    else: usage()
    if "--openhtml" in sys.argv :
        for path in created_html_files :
            os.system("xdg-open " + path)
