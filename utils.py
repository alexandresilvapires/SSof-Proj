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
        returns the vunerability, the source, the sink, and if it the source was sanitized 
        Only checks explicit flows"""

    def getSourceFromVar(tainted_vars, varID):
        """ Given a var ID and the tainted_vars dict, returns the source of the taint recursively"""
        curvar = varID
        while(tainted_vars[curvar]["source"] != curvar):
            curvar = tainted_vars[curvar]["source"]

            # Case for uninitialized vars
            if(curvar not in tainted_vars.keys()):
                return curvar
        return curvar
        
    # Dictionary with tainted vars. Each var is associated with a dict, which has:
    # a bool - "sanitized" - where it is true if the var has been sanitized
    # a string - "source" - with the source id, that is, the variable that tainted it 
    #           (if this variable has another source, it gets this value instead, recursively) 
    #           If the var is not initialized, or the taint comes from a entry point,
    #           the source is its own ID
    tainted_vars = {}
    
    # Keeps track of instantiated variables, since
    # by default uninstantiated vars are to be considered vunerable
    instantiated_vars = []
    
    assigns = getNodesOfType(tree, "Assign")
    
    #TODO: CHECK FOR CHAINED FUNCTIONS
    #      Check sink outside assignments
    #           eg: sink(a) 
    #      Return all possible vuns, not just the first found
    #      Add sanitized flows (list of sanitization functions used)
    
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


        # Check for any vars that were attributed the value of a tainted var (even if as arg)
        for v in varIDs:
            if(v in tainted_vars or v not in instantiated_vars):
                tainted += 1
                
        # Check for sanitization:
        # For every call made, if the arg was tainted, set sanitized bool to true
        # and lower tainted int, so if tainted == 0 in the end, we can assume only sanitized functions were given
        isSanitized = False
        for c in calls:
            if(getFunctionNameFromCall(c) in sanitization):        
                for v in varIDs:
                    if(getFunctionNameFromCall(c) in sanitization and v in getArgsIDFromCall(c)
                        and v in tainted_vars.keys() and tainted_vars[v]["sanitized"] == False):
                        
                        isSanitized = True
                        tainted -= 1
        
        
        # If anything was tainted, add every target ID to the list of tainted vars, as unsanitized
        # and add the uninstantiated vars as tainted too
        if(tainted != 0):

            # Used to know who was the source
            taintedVarForSource = None

            # Add uninstantiated vars to the list 
            for v in varIDs:
                if(v not in instantiated_vars and v not in tainted_vars.keys()):
                    tainted_vars[v] = {"sanitized":False, "source": v}
                if(v in tainted_vars.keys()):
                    taintedVarForSource = v
                
            taintedVarForSource = getSourceFromVar(tainted_vars, taintedVarForSource)

            for v in targetIDs:
                if(v not in tainted_vars.keys()):
                    tainted_vars[v] = {"sanitized":False, "source":taintedVarForSource}
            
        # Update tainted values
        elif(tainted == 0):
            if(isSanitized):
                # If anything is sanitized, and no taints were made (tainted == 0),
                # then the variables were totally sanitized, 
                # so every target ID's sanitization value is set to true
                for v in targetIDs:
                    tainted_vars[v]["sanitized"] = True
            else:
                # Every target ID is now clean, as the value attributed is totally clean
                for value in targetIDs:
                    if(value in tainted_vars):
                        tainted_vars.pop(value)
                        
        # Update list of instantiated values with all the values from the target
        for v in targetIDs:
            if(v not in instantiated_vars):
                instantiated_vars.append(v)
        
        # If any tainted var is given as an argument for a sink, return source and sink
        for sink in sinks:
            if(sink in calledIDs):
                call = getCallsWithID(a, sink)
                sink_args = []
                # can call the sink more than once!
                for c in call:
                    sink_args += getArgsIDFromCall(c)
                
                for t in tainted_vars.keys():
                    if(t in sink_args):
                        return tainted_vars[t]["source"], sink, tainted_vars[t]["sanitized"]

    return None, None, None