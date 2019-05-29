import os.path, sys, glob, datetime, time, subprocess, shutil, re, xml.sax.saxutils

def usage() :
    print "USAGE: testing.py --run"
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

chora = dict() 
chora["ID"] = "chora"
chora["displayname"] = "CHORA"
chora["cmd"] = [parent(2,testroot) + "/duet.native","-chora","{filename}"]

def defaulting_field(d,*fields) :
    if len(fields) == 0 :
        print "TEST SCRIPT ERROR: missing field in tool description: " + str(d)
    if fields[0] in d : return d[fields[0]]
    return defaulting_field(d,*fields[1:])

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

# TODO: allow for timing of multiple trials
class Datfile :
    def __init__(self, datpath) :
        datcellregex = re.compile("([^=\t]+=[^\t]+)")
        self.data = dict()
        with open(datpath,"rb") as dat :
            for line in dat :
                if len(line.strip()) == 0 : continue
                cellpairs = [C.split("=",1) for C in datcellregex.findall(line)]
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

tool_dicts = [chora]

alltools = {D["ID"]:Tool(D) for D in tool_dicts}

batch = dict()
batch["files"] = glob.glob(testroot + "/RBA_*.c")
batch["timeout"] = 300
batch["toolIDs"] = sorted(alltools.keys())
batch["style"] = "rba"

def reformat_float_string(s,form) :
    try :
        return form % float(s)
    except :
        return s

class HTMLTable :
    def __init__(self) :
        self.columns = list()
        self.rows = list()
        self.data = dict()
        self.style = "border='1px'"
    def register_row(self,rowid) :
        if rowid not in self.rows : self.rows.append(rowid)
    def register_column(self,colid) :
        if colid not in self.columns : self.columns.append(colid)
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
        rows = self.rows
        columns = self.columns
        for row in rows :
            output += "<tr>"
            for col in columns :
                output += "<td>" + self.get(row,col) + "</td>"
            output += "</tr>\n"
        output += "</table>\n"
        return output

def rba_callout(path) :
    output = ""
    with open(path,"rb") as logfile :
        mode = 0
        for line in logfile :
            if mode == 0 : 
                if line.startswith("---- Summary of"):
                    output += line
                    mode = 1
                    continue
            if mode == 1 :
                if line.startswith("Procedure: "):
                    mode = 2
                    continue
            if mode == 2 :
                if line.startswith("-----"):
                    mode = 0
                    continue
                output += line
    return output

def run(batch, stamp) :
    tools = [alltools[I] for I in batch["toolIDs"]]
    print "RUN ID=" + stamp
    outroot = testroot + "/output"
    outrun = outroot + "/" + stamp
    runlogpath = outrun + "/run.dat"
    outsources = outrun + "/sources/"
    makedirs(outsources)
    print ""
    with open(runlogpath,"wb") as runlog :
        for filename in sorted(batch["files"]) :
            nicename = filename
            if nicename.startswith(testroot+"/") : nicename = nicename[len(testroot)+1:]
            sys.stdout.write(" " + nicename + " ")
            shutil.copyfile(filename, outsources + nicename)
            for tool in tools : 
                cmd = [S.format(filename=filename) for S in tool.cmd]
                logfilename = outrun + "/logs/" + nicename + "." + tool.ID + ".log"
                makedirs(os.path.dirname(logfilename))
                startTime = time.time()
                exitType = "unknown"
                sys.stdout.write("["+tool.ID+":")
                timeTaken = -1.0
                with open(logfilename,"w") as logfile :
                    child = subprocess.Popen(cmd, stdout=logfile, stderr=subprocess.STDOUT)
                    while True :
                        timeTaken = time.time() - startTime
                        if child.poll() is not None : 
                            exitType = "default"
                            sys.stdout.write("OK] ")
                            sys.stdout.flush()
                            break
                        if timeTaken >= batch["timeout"] :
                            child.kill()
                            exitType = "timeout"
                            sys.stdout.write("T/O] ")
                            sys.stdout.flush()
                runlogline = ""
                runlogline += "source="+nicename+"\t"
                runlogline += "tool="+tool.ID+"\t"
                runlogline += "exit="+exitType+"\t"
                runlogline += "time="+str(timeTaken)+"\t"
                print >>runlog, runlogline
            print "" 

    newstamp = datetime.datetime.now().strftime("%Y/%m/%d at %H:%M:%S")
    print ""
    print "Run ID=" + stamp + " completed at " + newstamp

    format_run(outrun, batch["style"])

def format_run(outrun, style) :
    if not os.path.isdir(outrun) : 
        outrun = testroot + "/output/" + outrun
    if not os.path.isdir(outrun) : 
        print "Wasn't a directory: " + outrun
        usage()
    if style == "rba" :
        htmlpath = outrun+"/rba.html"
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
            sourcefiles = sorted(sourcefiles)

            logtoolIDs = list()
            logroot = outrun+"/logs/"
            toolre = re.compile(".*[.](.*)[.]log$")
            for curdir, dirs, files in os.walk(logroot):
                for filename in files :
                    if not filename.endswith(".log") : continue
                    matches = toolre.match(filename)
                    if matches :
                        logtoolIDs.append(matches.group(1))
            logtoolIDs = sorted(set(logtoolIDs))
            tools = list()
            for toolID in logtoolIDs :
                if toolID in alltools :
                    tools.append(alltools[toolID])
                else :
                    print "WARNING: unrecognized tool ID: " + toolID
                    print "         Creating a default tool with that name."
                    tools.append(Tool({"ID":toolID}))

            table = HTMLTable()

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
                    table.set(sourcefilekey,"toolrba/"+tool.ID,"<pre>"+xml.sax.saxutils.escape(rba_callout(logpath))+"</pre>")
                    loglinks.append("<a href='logs/" + logrel + "'>[" + tool.ID + "]</a>")
                table.set(sourcefilekey,"logs"," ".join(loglinks))
            print >>html, table.show()
            print >>html, "</body></html>"
    else :
        print "Unrecognized formatting style requested: " + style

if __name__ == "__main__" :
    if len(sys.argv) < 2 : usage()
    if sys.argv[1] == "--run" : 
        stamp = datetime.datetime.now().strftime("%Y_%m_%d_at_%H_%M_%S")
        for arg in sys.argv :
            matches = re.match("--stamp=(.*)",arg)
            if matches :
                stamp = matches.group(1)
                break
        run(batch,stamp)
    elif sys.argv[1] == "--format" :
        if len(sys.argv) < 3 : usage()
        outrun = sys.argv[2]
        style = "rba" # someday, style="default"
        if "style=rba" in sys.argv : style = "rba"
        format_run(outrun, style)
    else: usage()
