import os.path, re, sys

def makedirs(d) :
    if os.path.exists(d) : return
    os.makedirs(d)
def parent(k,d) :
    if k == 0 : return d
    return parent(k-1,os.path.dirname(d))

this_script_dir = parent(1,os.path.realpath(__file__)) 
testroot = parent(2,os.path.realpath(__file__))
benchroot = os.path.join(testroot,"benchmarks/")
config_path = os.path.join(this_script_dir,"local-test-settings.conf")
blank_config = """\
# Please edit this file with the local paths to various tool installations on your machine

# This should be the directory containing the duet.native binary
chora_root=%s

# This should be the directory containing the icra binary
icra_root=

# This should be the directory containing the duet.native binary
duetcra_root=
""" % parent(4,os.path.realpath(__file__))
config = dict()
if not os.path.exists(config_path) :
    with open(config_path,"wb") as config_file :
        print >>config_file, blank_config
with open(config_path,"rb") as config_file :
    for line in config_file :
        if len(line.strip()) == 0 or "=" not in line : continue
        parts = line.split("=",1)
        if len(parts[1].strip()) == 0 : continue
        config[parts[0].strip()]=parts[1].strip()

if "suppress_color" not in config or not config["suppress_color"] :
    color_start = "\033[91m"
    color_stop = "\033[0m"
else :
    color_start = ""
    color_stop = ""

def require_config(key, message) :
    if key in config : return config[key]
    print "Please add a line to your local configuration file\n    " + config_path + "\nof the form:"
    print "    " + key + "=" + message
    sys.exit(0)

def specify_tool_root_requirement(ID, binary_relative_path_suggestion=None) :
    if ID + "_root" in config : return config[ID + "_root"]
    if binary_relative_path_suggestion is not None :
        require_config(ID + "_root", 
                       "<ROOTDIR>\nsuch that the " + ID + " tool binary is found at <ROOTDIR>/"
                       +binary_relative_path_suggestion + " on your machine")
    require_config(ID + "_root",
                   "<ROOTDIR>\nsuch that <ROOTDIR> is the root directory of the tool " + ID + " on your machine")

def get_tool_root(ID) :
    if ID + "_root" in config : return config[ID + "_root"]
    tool = get_tool_by_ID(ID,False)
    if tool is not None :
        return tool.get("root")
    require_config(ID + "_root",
                   "<ROOTDIR>\nsuch that <ROOTDIR> is the root directory of the tool " + ID + " on your machine")

scriptroot = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0,scriptroot)

##

class StringRing :
    def __init__(self, length) :
        self.length = length
        self.ring = list() 
        for i in range(self.length) : self.ring.append("")
        self.cursor = 0
    def advance(self) :
        self.cursor = (self.cursor + 1) % self.length
    def add(self, line) :
        self.ring[self.cursor] = line
        self.advance()
    def readout(self) :
        output = ""
        self.advance()
        for i in range(self.length) :
            line = self.ring[self.cursor]
            if line != "" : 
                if output != "" : output += "\n"
                output += line
            self.advance()
        return output

def generic_error_callout(params) :
    if "logpath" not in params : 
        print "ERROR: generic_error_callout was called without a path"
        sys.exit(0)
    ring = StringRing(5)
    # It probably isn't safe to say "error" here; that word is used
    #   too often in non-exceptional cases.
    errorRegex = re.compile("failure|fatal|exception",re.IGNORECASE)
    with open(params["logpath"],"rb") as logfile :
        mode = 0
        for line in logfile :
            if len(line.strip()) == 0 : continue
            if errorRegex.search(line) :
                ring.add(line.rstrip())
    return ring.readout()

##

def defaulting_field(d,kind,*fields) :
    if len(fields) == 0 :
        print "TEST SCRIPT ERROR: missing field in "+kind+" description: " + str(d)
    if fields[0] in d : return d[fields[0]]
    return defaulting_field(d,kind,*fields[1:])

def enforce_rules(kind, d) :
    if kind == "tool" :
        d["displayname"] = defaulting_field(d,kind,"displayname","ID")
        d["shortname"] = defaulting_field(d,kind,"shortname","ID")
        for req in ["cmd"] :
            if req not in d : 
                print "ERROR: " + kind + " component " + d["ID"] + " does not define " + req
                sys.exit(0)
    elif kind == "batch" :
        pass
    else :
        raise Exception("Unknown component kind: " + kind)

class Component :
    def __init__(self, d, kind, ID) :
        # We could put the contents of d into __dict__, but if we
        #   avoid doing so, that enforces a little more orderliness
        d["ID"] = ID
        enforce_rules(kind, d)
        self.d = d
        self.ID = ID
    def hasattr(self, attr) : return (attr in self.d)
    def get(self, attr) : return self.d[attr]
    def flag(self, attr) :
        return self.hasattr(attr) and (self.get(attr) == True)

##

defdirs = dict()
defdirs["tool"] = os.path.join(scriptroot,"tooldefs")
defdirs["batch"] = os.path.join(scriptroot,"batchdefs")

loaded_components = dict()

def get_component_by_ID(kind, ID, exit_on_failure=True) :
    if kind not in loaded_components :
        loaded_components[kind] = dict()
    if ID in loaded_components[kind] :
        return loaded_components[kind][ID]
    for py in os.listdir(defdirs[kind]) :
        if py == kind+"_"+ID+".py" :
            component_module = getattr(__import__(kind+"defs."+kind+"_"+ID),kind+"_"+ID)
            if not hasattr(component_module,kind) :
                if not exit_on_failure : return None
                print "ERROR: No "+kind+" variable was defined by the "+kind+" module "+kind+"defs/"+kind+"_"+ID+".py"
                sys.exit(0)
            comp = Component(getattr(component_module,kind),kind,ID)
            loaded_components[kind][ID] = comp
            return comp
    else :
        if not exit_on_failure : return None
        print "Unrecognized "+kind+" ID: " + ID
        print_known_components(kind)
        sys.exit(0)

def clone_component(kind, ID) :
    return dict(get_component_by_ID(kind, ID).d)

def print_known_components(kind) : 
    known_components = list()
    for py in os.listdir(defdirs[kind]) :
        if py.startswith(kind+"_") and py.endswith(".py") :
            known_components.append(py[len(kind+"_"):-len(".py")])
    print "Valid "+kind+" IDs are: " + str(known_components)

##

def get_tool_by_ID(ID,f=True) : return get_component_by_ID("tool",ID,f)
def clone_tool(ID) : return clone_component("tool",ID)
def print_known_tools() : return print_known_components("tool")
def get_default_tool_dict() : return dict()

##

def get_batch_by_ID(ID,f=True) : return get_component_by_ID("batch",ID,f)
def clone_batch(ID) : return clone_component("batch",ID)
def print_known_batches() : return print_known_components("batch")
def get_default_batch_dict() :
    batch = dict()
    batch["timeout"] = 300
    batch["toolIDs"] = ["chora"]
    batch["root"] = benchroot
    batch["format_alternate_bgcolor"] = True
    batch["format_style"] = "assert"
    return batch


