# Utils for the various functions of the bo-analyser

# JSON Program utils

def getLines(tree):
    return tree["body"]

def getLine(tree, line):
    for l in getLines(tree):
        if(l["lineno"] == line):
            return l
    return None

# TODO:
# Check if the given line has a given function
# Get all usages of a certain variable
# Check taint: give an infected function, and returns all variables infected by it 
# Check taint 2: give an infected function and a sink and sanitizer, and check if they ever each those


def getNodesOfType(tree, type):
    """Returns the a list of nodes with a certain type"""
    nodes = []

    #List that contains every type of node the program includes
    #toCheck = ["Constant","Name","Expr","BinOp","Compare","Call","Attribute","Assign","If","While"]
    if(tree["ast_type"] == "Constant"):
        if(type == "Constant"):
            nodes += [tree]
        return nodes

    elif(tree["ast_type"] == "Name"):
        if(type == "Name"):
            nodes += [tree]
        return nodes

    elif(tree["ast_type"] == 'Expr'):
        if(type == "Expr"):
            nodes += [tree]
        return nodes + getNodesOfType(tree["value"], type)

    elif(tree["ast_type"] == "BinOp"):
        if(type == "BinOp"):
            nodes += [tree]
        return nodes + getNodesOfType(tree["right"], type) + getNodesOfType(tree["left"], type)

    elif(tree["ast_type"] == "Compare"):
        if(type == "Compare"):
            nodes += [tree]
        for comps in tree["comparators"]:
            nodes += getNodesOfType(comps, type)
        return nodes + getNodesOfType(tree["left"], type)

    elif(tree["ast_type"] == "Call"):
        if(type == "Call"):
            nodes += [tree]
        if("args" in tree.keys()):
            for arg in tree["args"]:
                nodes += getNodesOfType(arg, type)
        return nodes + getNodesOfType(tree["func"], type)

    elif(tree["ast_type"] == "Attribute"):
        if(type == "Attribute"):
            nodes += [tree]
        return nodes +  getNodesOfType(tree["value"], type) 

    elif(tree["ast_type"] == "Assign"):
        if(type == "Assign"):
            nodes += [tree]
        for t in tree["targets"]:
            nodes += getNodesOfType(t, type)
        return nodes +  getNodesOfType(tree["value"], type) 

    elif(tree["ast_type"] == "If"):
        if(type == "If"):
            nodes += [tree]
        for stmt in tree["body"]:
            nodes += getNodesOfType(stmt, type)
        for stmt in tree["orelse"]:
            nodes += getNodesOfType(stmt, type)
        return nodes +  getNodesOfType(tree["test"], type) 

    elif(tree["ast_type"] == "While"):
        if(type == "While"):
            nodes += [tree]
        for stmt in tree["body"]:
            nodes += getNodesOfType(stmt, type)
        for stmt in tree["orelse"]:
            nodes += getNodesOfType(stmt, type)
        return nodes +  getNodesOfType(tree["test"], type) 

    elif(tree["ast_type"] == "Module"):
        for stmt in tree["body"]:
            nodes += getNodesOfType(stmt, type)
        return nodes

    else:
        return nodes


def getCallsWithID(tree, id):
    calls = []
    funcs = getNodesOfType(tree, "Call")
    
    for f in funcs:
        if(f["func"]["ast_type"] == "Name"):
            if("id" in f["func"].keys() and f["func"]['id'] == id):
                calls = calls + [f]

        elif(f["func"]["ast_type"] == "Attribute" and "attr" in f["func"].keys()):
            if(f["func"]['attr'] == id):
                calls = calls + [f]
    return calls

def getAssignmentsFromVarWithID(tree, id):
    """Given a tree and an ID of a variable, returns the list of assignments where
        the given variable was used as the value of the assignment"""
    assignments = []
    assigns = getNodesOfType(tree, "Assign")
    
    for a in assigns:
        if(a["value"]["ast_type"] == "Name" and a["value"]["id"] == id):
                assignments = assignments + [a]
    return assignments

def getVarsAssinedAsTargetWithID(tree, id):
    """Given a tree and an ID of a variable, returns the list of IDs of vars 
        that where assigned a value of the given variable ID"""
    assignments = []
    assigns = getAssignmentsFromVarWithID(tree, id)
    
    for a in assigns:
        for t in a["targets"]:
            if(t["value"]["ast_type"] == "Name"):
                    assignments = assignments + [t["value"]["id"] ]
    return assignments

def getArgsIDFromCall(tree):
    """Given a tree that is a call, returns a list of IDs of each arg"""

    vars = []
    if("args" in tree.keys()):
        for a in tree["args"]:
            names = getNodesOfType(a, "Name")
            for n in names:
                vars.append(n["id"])
    return vars

def getTargetIDInAssignment(tree):
    """Given a tree that is an assignment, returns a list of IDs of the vars that were assigned"""

    vars = []
    for vt in tree["targets"]:
        targets = getNodesOfType(vt, "Name")
        for t in targets:
            vars.append(t["id"])
    
    return vars

def getFunctionNameFromCall(tree):
    """Given a tree that is a call, returns the name of the function called"""
    
    #Check for calls like a.func()
    atr = getNodesOfType(tree,"Attribute")
    if(atr != []):
        return atr[0]["attr"]
    #Check for calls like func()
    else:
        return tree["func"]["id"]

def getVarsUsedAsValue(tree):
    """ Given a tree that is an assignment, returns the list of variable ids used
        in the assignment, INCLUDING VARS USED AS FUNCTION ARGS"""
        
    # Terrible way to do this, get every named node, get every name that is from a function
    # and return the remaining names
    names = []
    
    funcCalls = getNodesOfType(tree["value"], "Call")
    funcNames = []
    for c in funcCalls:
        funcNames.append(getFunctionNameFromCall(c))
    
    nameNodes = getNodesOfType(tree["value"],"Name")
    for n in nameNodes:
        if(n["id"] not in funcNames and n["id"] not in names):
            names.append(n["id"])
            
    return names

def removeDupesFromList(l):
    return list(set(l))

def trackTaint(tree, entry_points, sanitization, sinks):
    """ Given a list of entry points, sanitization functions and sinks,
        returns true if any reached the sinks.
        Only checks explicit flows (?)"""
    tainted_vars = []
    
    assigns = getNodesOfType(tree, "Assign")
    
    #TODO:  CHECK FOR SANITIZATION!!!
    #       CHECK FOR CHAINED FUNCTIONS
    #       GIVE CORRECT INPUT
    
    for a in assigns:
        tainted = 0         # turns into a different value if a entry point or 
                            # tainted var is used in assignment

        calls = getNodesOfType(a, "Call")
        calledIDs = []

        for c in calls:
            calledIDs.append(getFunctionNameFromCall(c))
            
        varIDs = getVarsUsedAsValue(a)
        
        targetIDs = getTargetIDInAssignment(a)
        
        #Check if assigned value was entry point or tainted vars and add to list
        for e in entry_points:
            # If any was, add each target to the list of tainted vars
            if(e in calledIDs):
                tainted += 1
                tainted_vars += targetIDs
                tainted_vars = removeDupesFromList(tainted_vars)


        # Check for any vars that were attributed the value of a tainted var (even if as arg)
        for v in varIDs:
            if(v in tainted_vars):
                tainted += 1
                tainted_vars += targetIDs
                tainted_vars = removeDupesFromList(tainted_vars)
                
        print("tainted vars:", tainted_vars)
                    
        #If any tainted var is assigned a non tainted value, it is no longer tainted
        if(tainted == 0):
            for value in targetIDs:
                if(value in tainted_vars):
                    tainted_vars.remove(value)
        
        #If any tainted var is given as an argument for a sink, return source and sink
        for sink in sinks:
            if(sink in calledIDs):
                call = getCallsWithID(a, sink)
                sink_args = []
                #can call the sink more than once!
                for c in call:
                    sink_args += getArgsIDFromCall(c)
                
                for t in tainted_vars:
                    if(t in sink_args):
                        return t, sink

    return None, None