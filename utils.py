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
        if(type == "Constante"):
            nodes += [tree]
        return nodes

    elif(tree["ast_type"] == "Name"):
        if(type == "Name"):
            nodes += [tree]
        return nodes

    elif(tree["ast_type"] == 'Expr'):
        if(type == "Expr"):
            nodes += [tree]
        return nodes + getNodesOfType(tree, type)

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
        names = getNodesOfType(tree["args"], "Name")
        for n in names:
            vars.append(n["id"])
    return vars

def getTargetIDInAssignment(tree):
    """Given a tree that is an assignment, returns a list of IDs of the vars that were assigned"""

    vars = []
    targets = getNodesOfType(tree["targets"], "Name")
    for t in targets:
        vars.append(t["id"])
    return vars

def removeDupesFromList(l):
    return list(set(l))

def trackTaint(tree, entry_points, sanitization, sinks):
    """ Given a list of entry points, sanitization functions and sinks,
        returns true if any reached the sinks.
        Only checks explicit flows (?)"""
    tainted_vars = []
    
    assigns = getNodesOfType(tree, "Assign")
    
    #TODO: CHECK FOR SANITIZATION!!!
    
    #Check if assigned value was entry point or tainted vars and add to list
    for a in assigns:
        #Check if any entry points where called
        for e in entry_points:
            # If any was, add each target to the list of tainted vars
            if(getCallsWithID(a, e)):
                tainted_vars = tainted_vars + getTargetIDInAssignment(a)
                tainted_vars = removeDupesFromList(tainted_vars)

        for t in tainted_vars:
            # Check for any vars that were attributed the value of a tainted var
            tainted_vars = tainted_vars + getVarsAssinedAsTargetWithID(a, t)
            
            # Check for any vars that were attributed the value of a function whose args were tainted
            calls = getNodesOfType(a, "Call")
            for c in calls:
                args = getArgsIDFromCall(c)
                if(t in args):
                    tainted_vars = tainted_vars + getTargetIDInAssignment(a)
                    tainted_vars = removeDupesFromList(tainted_vars)
            
            
    
    #Check if any of the tainted values ever reached a sink
    #TODO: THIS DOES NOT TAKE IN CONSIDERATION ORDER; SHOULD BE INSIDE FORS OF ASSIGNS WITH LINE CONSIDERATION
    calls = getNodesOfType(tree, "Call")
    for c in calls:
        args = getArgsIDFromCall(c)
        for t in tainted_vars:
            if(t in args):
                return True
    return False