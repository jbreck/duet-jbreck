#!/usr/bin/python
import os.path, sys, glob, datetime, time, subprocess, shutil, re
import xml.sax.saxutils, csv, tempfile

def usage() :
    print "USAGE: testing.py --run <batchname>"
    print "         to start a new testing run"
    print "   OR  testing.py --format <dir> [<options>...]"
    print "         to reformat the results of the previous testing run in <dir>"
    sys.exit(0)
def makedirs(d) :
    if os.path.exists(d) : return
    os.makedirs(d)
def parent(k,d) :
    if k == 0 : return d
    return parent(k-1,os.path.dirname(d))

testroot = parent(2,os.path.realpath(__file__))
benchroot = os.path.join(testroot,"benchmarks/")

# Note to self: output parsing needs to be attached to specific tools

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
            if mode == 0 : 
                if line.startswith("---- Bounds on"):
                    output += line
                    #mode = 1
                    mode = 2 
                    continue
            #if mode == 1 :
            #    if line.startswith("Procedure: "):
            #        mode = 2
            #        continue
            if mode == 2 :
                if line.startswith("-----"):
                    mode = 0
                    continue
                output += line
    return output

chora = dict() 
chora["ID"] = "chora"
chora["displayname"] = "CHORA"
chora["cmd"] = [parent(2,testroot) + "/duet.native","-chora","{filename}"]
chora["bounds_callout"] = chora_bounds_callout
chora["assert_results"] = chora_assert_results


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
icra = dict() 
icra["ID"] = "icra"
icra["displayname"] = "ICRA"
icra["cmd"] = ["/u/j/b/jbreck/research/2013/ICRA/icra/icra","{filename}"]
icra["bounds_callout"] = icra_bounds_callout
icra["assert_results"] = icra_assert_results


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
duetcra = dict() 
duetcra["ID"] = "duetcra"
duetcra["displayname"] = "CRA"
duetcra["shortname"] = "cra"
duetcra["cmd"] = ["/u/j/b/jbreck/research/2013/ICRA/icra/duet/duet.native",
                  "-cra","{filename}","-test","{tmpfile}"]
duetcra["bounds_callout"] = duet_bounds_callout
duetcra["assert_results"] = duet_assert_results
duetcra["no_assert_line_numbers"] = True

duetrba = dict() 
duetrba["ID"] = "duetrba"
duetrba["displayname"] = "CRA:rba"
duetrba["shortname"] = "cra"
duetrba["cmd"] = ["/u/j/b/jbreck/research/2013/ICRA/icra/duet/duet.native",
                  "-rba","{filename}","-test","{tmpfile}"]
duetrba["bounds_callout"] = duet_bounds_callout
duetrba["assert_results"] = duet_assert_results
duetcra["no_assert_line_numbers"] = True


def defaulting_field(d,*fields) :
    if len(fields) == 0 :
        print "TEST SCRIPT ERROR: missing field in tool description: " + str(d)
    if fields[0] in d : return d[fields[0]]
    return defaulting_field(d,*fields[1:])

def yes_post_slash(d) :
    if d[-1] == "/" : return d
    return d + "/"

tool_IDs = set()
class Tool :
    def __init__(self, d) :
        global tool_IDs
        self.d = d
        self.ID = d["ID"]
        if not re.match("([a-z]|[A-Z]|[0-9]|-|_)+", self.ID) :
            print "TEST SCRIPT ERROR: a tool ID may be only alphanumeric with dashes and underscores: " + self.ID
            sys.exit(0)
        if self.ID in tool_IDs :
            print "TEST SCRIPT ERROR: there is more than one tool with the same ID: " + self.ID
            sys.exit(0)
        tool_IDs.add(self.ID)
        self.cmd = d["cmd"]
        self.displayname = defaulting_field(d,"displayname","ID")
        self.shortname = defaulting_field(d,"shortname","ID")
    def has(self, attr) : return attr in self.d
    def get(self, attr) : return self.d[attr]
    def hastrue(self, attr) :
        return self.has(attr) and (self.get(attr) == True)

# TODO: allow for timing of multiple trials
class Datfile :
    def __init__(self, datpath) :
        #datcellregex = re.compile("([^=\t]+=[^\t]+)")
        self.data = dict()
        with open(datpath,"rb") as dat :
            csvreader = csv.reader(dat, delimiter="\t")
            #for line in dat :
            for row in csvreader :
                #if len(line.strip()) == 0 : continue
                if len(row) == 0 : continue
                #cellpairs = [C.split("=",1) for C in datcellregex.findall(line)]
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

#tool_dicts = [chora, icra, duetcra, duetrba]
tool_dicts = [duetcra, duetrba, icra, chora]

alltools = {D["ID"]:Tool(D) for D in tool_dicts}

def detect_safe_benchmark(path) :
    # return "safe" or "unsafe" or "mixed"
    basename = os.path.basename(path)
    if (('unsafe' in basename) or ('false-unreach-call' in basename)) :
        return "unsafe"
    return "safe"

bbatch = dict()
bbatch["timeout"] = 300
#bbatch["toolIDs"] = sorted(alltools.keys())
bbatch["toolIDs"] = ["chora"]
bbatch["root"] = benchroot

rbabatch = dict(bbatch)
rbabatch["ID"] = "rba"
rbabatch["files"] = glob.glob(benchroot + "rba/*.c")
rbabatch["format_style"] = "rba"
rbabatch["warmupfiles"] = ["rba/cost_fib.c","rba/cost_fib_eq.c"]

abatch = dict(bbatch)
abatch["ID"] = "assert"
abatch["files"] = glob.glob(benchroot + "assert/chora_simple/*.c")
abatch["format_style"] = "assert"

allassert = dict(abatch)
allassert["ID"] = "allassert"
allassert["toolIDs"] = ["duetcra", "icra", "chora"]

#allrba["toolIDs"] = ["chora", "icra", "duetrba"]

#maybe say which is which?

c4b = dict(bbatch)
c4b["ID"] = "c4b"
c4b["root"] = "/u/j/b/jbreck/research/2013/ICRA/icra/WALi-OpenNWA/Examples/cprover/tests/"
c4b["files"] = glob.glob(c4b["root"] + "c4b/*.c")
c4b["format_style"] = "assert"

icrabatch = dict(bbatch)
icrabatch["ID"] = "icra"
icrabatch["root"] = "/u/j/b/jbreck/research/2013/ICRA/icra/WALi-OpenNWA/Examples/cprover/tests/"
# Small, for quick testing:
#icrabatch["files"] = (glob.glob(icrabatch["root"] + "c4b/*.c")[:4] + 
#                      glob.glob(icrabatch["root"] + "sv-benchmarks/loops/*.c")[-4:])
# Too big:
#icrabatch["files"] = [F for F in [os.path.join(R,F) for R,D,Fs in os.walk(icrabatch["root"]) for F in Fs] if F.endswith(".c")]
icra_dirs = ["c4b", "misc-recursive", "duet", "", "STAC/polynomial/assert", 
"snlee/snlee_tests", "STAC/FiniteDifferencing", "STAC/LESE", "STAC/LowerBound", 
"STAC/LZ", "sv-benchmarks/loop-acceleration", "sv-benchmarks/loop-invgen", 
"sv-benchmarks/loop-lit", "sv-benchmarks/loop-new", "sv-benchmarks/loops", 
"sv-benchmarks/recursive", "sv-benchmarks/recursive-simple", 
"rec-sv-benchmarks/rec-loop-lit", "rec-sv-benchmarks/rec-loop-new", 
"recurrences", "exponential", "frankenstein/HOLA", "frankenstein/relational", 
"misc2017", "max_equals", "branching_loops", "strings_numeric", "ethereum"]
# maybe make this a lambda?
icrabatch["files"] = []
try :
    icrabatch["files"] = [os.path.join(icrabatch["root"],D,F) for D,Fs in 
           [(D, os.listdir(os.path.join(icrabatch["root"],D))) for D in icra_dirs]
        for F in Fs if F.endswith(".c")] 
except : pass
icrabatch["format_style"] = "assert"
icrabatch["toolIDs"] = ["duetcra","icra","chora"]

batch_dicts = [rbabatch, abatch, c4b, icrabatch, allassert]

allbatches = {D["ID"]:D for D in batch_dicts}

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
    if (conclusion == "NO_ASSERTS") :
        return '<font color=\"#000000\">NO_ASSERTS</font><br>'
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

def aggregate_assert_results(assert_str, exitType, is_safe, style) :
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
            out["conclusion"] = "NO_ASSERTS"
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
        else :
            out["conclusion"] = "MIXED"
    else :
        out["conclusion"] = "UNKNOWN"
    conclusion_html = ("<span title='"+ 
                       "exitType="+exitType+",  asserts="+assert_str+"'>"+
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

class HTMLTable :
    def __init__(self) :
        self.columns = list()
        self.rows = list()
        self.data = dict()
        self.style = "border='1px'"
        self.prefix = ""
    def register_row(self,rowid) :
        if rowid not in self.rows : self.rows.append(rowid)
    def register_column(self,colid) :
        if colid not in self.columns : self.columns.append(colid)
    def set_prefix(self, prefix) : self.prefix = prefix
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
    def show(self) :
        output = "<table " + self.style + " >\n"
        output += self.prefix
        rows = self.rows
        columns = self.columns
        for row in rows :
            output += "<tr>"
            for col in columns :
                output += "<td>" + self.get(row,col) + "</td>"
            output += "</tr>\n"
        output += "</table>\n"
        return output

def sort_dir_major(f) : return ( os.path.dirname(f), os.path.basename(f) )

def run(batch, stamp) :
    tools = [alltools[I] for I in batch["toolIDs"]]
    print "RUN ID=" + stamp
    outroot = testroot + "/output"
    outrun = outroot + "/" + stamp
    runlogpath = outrun + "/run.dat"
    outsources = outrun + "/sources/"
    makedirs(outsources)
    formatting = []
    formatting.append("format_toolIDs="+",".join(batch["toolIDs"]))
    for key in batch :
        if key.startswith("format_") :
            formatting.append(key+"="+batch[key])
    formattingpath = outrun + "/formatdata.txt"
    with open(formattingpath, "wb") as formatfile :
        for line in formatting :
            print >>formatfile, line
    if not "root" in batch:
        print "ERROR: batch['root'] was not specified"
        return
    for filename in sorted(batch["files"]) :
        if not filename.startswith(batch["root"]) :
            print "ERROR: not all files in batch are under the batch['root']"
            print "   batch['root']="+str(batch["root"])
            print "   exceptional filename = "+str(filename)
            return
    if "warmupfiles" in batch and len(batch["warmupfiles"]) > 0 :
        print ""
        print "  Warmup..."
        with open(os.devnull, 'w') as devnull:
            for tool in tools : 
                for filename in batch["warmupfiles"] :
                    cmd = [S.format(filename=filename) for S in tool.cmd]
                    subprocess.call(cmd, stdout=devnull, stderr=devnull)
    print ""
    with open(runlogpath,"wb") as runlog :
        for filename in sorted(batch["files"], key=sort_dir_major) :
            nicename = filename
            br_prefix = yes_post_slash(batch["root"])
            if nicename.startswith(br_prefix) : nicename = nicename[len(br_prefix):]
            sys.stdout.write(" " + nicename + " ")
            sourcedest = outsources + nicename
            makedirs(os.path.dirname(sourcedest))
            shutil.copyfile(filename, sourcedest)
            for tool in tools : 
                handle, tmpfile = tempfile.mkstemp(suffix="choratmpfile.txt")
                os.close(handle)
                cmd = [S.format(filename=filename, tmpfile = tmpfile) for S in tool.cmd]
                logfilename = outrun + "/logs/" + nicename + "." + tool.ID + ".log"
                makedirs(os.path.dirname(logfilename))
                startTime = time.time()
                exitType = "unknown"
                sys.stdout.write("["+tool.ID+":")
                timeTaken = -1.0
                with open(logfilename,"w") as logfile :
                    print >>logfile, " ".join(cmd)
                    print >>logfile, ""
                    logfile.flush()
                    child = subprocess.Popen(cmd, stdout=logfile, stderr=subprocess.STDOUT)
                    while True :
                        timeTaken = time.time() - startTime
                        if child.poll() is not None :
                            if (child.returncode != 0 and
                               not tool.hastrue("nonzero_error_code_is_benign")) :
                                exitType = "error"
                                sys.stdout.write("ERROR] ")
                                sys.stdout.flush()
                                break
                            exitType = "default"
                            sys.stdout.write("OK] ")
                            sys.stdout.flush()
                            break
                        if timeTaken >= batch["timeout"] :
                            child.kill()
                            exitType = "timeout"
                            sys.stdout.write("T/O] ")
                            sys.stdout.flush()
                            break
                runlogline = ""
                runlogline += "source="+nicename+"\t"
                runlogline += "tool="+tool.ID+"\t"
                runlogline += "exit="+exitType+"\t"
                runlogline += "time="+str(timeTaken)+"\t"
                #trialNo = 0
                #runlogline += "trial="+trialNo+"\t" # maybe?
                if tool.has("assert_results") :
                    results = tool.get("assert_results")({"logpath":logfilename,"tmpfile":tmpfile})
                    if tool.has("no_assert_line_numbers") : 
                        result_str = ";".join(R[0]+"@?" for R in results)
                    else : 
                        results = sorted(results,key=lambda R:R[1])
                        result_str = ";".join(R[0]+"@"+str(R[1]) for R in results)
                    runlogline += "assert=["+result_str+"]\t"
                runlogline += "runid="+stamp+"\t"
                while len(runlogline) > 0 and runlogline[-1]=="\t" : runlogline = runlogline[:-1]
                print >>runlog, runlogline
                os.remove(tmpfile)
            print "" 

    newstamp = datetime.datetime.now().strftime("%Y/%m/%d at %H:%M:%S")
    print ""
    print "Run ID=" + stamp + " completed at " + newstamp

    format_run(outrun)

created_html_files = list()

def format_run(outrun) :
    if not os.path.isdir(outrun) : 
        outrun = testroot + "/output/" + outrun
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
            print >>html, "<html><body>"

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
                if toolID in alltools :
                    tools.append(alltools[toolID])
                else :
                    print "WARNING: unrecognized tool ID: " + toolID
                    print "         Creating a default tool with that name."
                    tools.append(Tool({"ID":toolID}))

            table = HTMLTable()
            table.prefix = """<colgroup> <col span="1" style="width:600px;"> </colgroup>\n"""

            if formatting["style"] == "rba" :
                # register rows and columns
                table.register_row("head")
                for sourcefile in sourcefiles : table.register_row("src/"+sourcefile)
                table.register_column("benchmark")
                table.register_column("logs")
                for tool in tools : 
                    table.register_column("tooltime/"+tool.ID)
                    table.register_column("toolrba/"+tool.ID)

                # fill in table
                table.set("head","benchmark","Benchmark")
                table.set("head","logs","Full<br>Logs")
                for tool in tools :
                    table.set("head","tooltime/"+tool.ID, tool.displayname + "<br>Time (s)")
                    table.set("head","toolrba/"+tool.ID, tool.displayname + "<br>Resource Bounds")
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
                        if tool.has("bounds_callout") : 
                            bc_result = ("<pre>"
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
                print >>html, table.show()
                print >>html, "</body></html>"
            if formatting["style"] == "assert" :
                # register rows and columns
                table.register_row("head")
                for sourcefile in sourcefiles : table.register_row("src/"+sourcefile)
                table.register_column("benchmark")
                table.register_column("logs")
                for tool in tools : 
                    table.register_column("tooltime/"+tool.ID)
                    table.register_column("toolassert/"+tool.ID)

                # fill in table
                table.set("head","benchmark","Benchmark")
                table.set("head","logs","Full<br>Logs")
                for tool in tools :
                    table.set("head","tooltime/"+tool.ID, tool.displayname + "<br>Time (s)")
                    table.set("head","toolassert/"+tool.ID, tool.displayname + "<br>Assertions")
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

                        assert_out = aggregate_assert_results(assert_str, exitType, is_safe, "short")

                        table.set(sourcefilekey, "toolassert/"+tool.ID, assert_out["html"])

                        if not os.path.exists(logpath) : continue
                        loglinks.append("<a href='logs/" + logrel + "'>[" + tool.shortname + "]</a>")
                    table.set(sourcefilekey,"logs"," ".join(loglinks))
                print >>html, table.show()
                print >>html, "</body></html>"

def list_known_batch_names() :
    keys = sorted(allbatches.keys())
    print "Known batch IDs are: [" + ", ".join(keys) + "]"

if __name__ == "__main__" :
    if len(sys.argv) < 3 :
        if "--run" in sys.argv :
            list_known_batch_names()
        usage()
    if sys.argv[1] == "--run" : 
        batchid = sys.argv[2]
        stamp = datetime.datetime.now().strftime("%Y_%m_%d_at_%H_%M_%S")
        for arg in sys.argv :
            matches = re.match("--stamp=(.*)",arg)
            if matches :
                stamp = matches.group(1)
            #matches = re.match("--batch=(.*)",arg)
            #if matches :
            #    batchid = matches.group(1)
        #if batchid is None :
        #    print "ERROR: need to supply a batch name with --batch=<name>"
        #    list_known_batch_names()
        #    sys.exit(0)
        if batchid not in allbatches :
            print "ERROR: unrecognized batch name"
            list_known_batch_names()
            sys.exit(0)
        run(allbatches[batchid],stamp)
    elif sys.argv[1] == "--format" :
        if len(sys.argv) < 2 : usage()
        outrun = sys.argv[2]
        format_run(outrun)
    else: usage()
    if "--openhtml" in sys.argv :
        for path in created_html_files :
            os.system("xdg-open " + path)
