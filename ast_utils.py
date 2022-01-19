# GENERAL FUNCTIONS

def getLines(tree):
    return tree["body"]

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
        return nodes + getNodesOfType(tree["value"], type) 

    elif(tree["ast_type"] == "If"):
        if(type == "If"):
            nodes += [tree]
        for stmt in tree["body"]:
            nodes += getNodesOfType(stmt, type)
        if("orelse" in tree.keys()):
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

# CALL FUNCTIONS

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

def getCallArgsID(tree):
    """Given a tree that is a call, returns a list of IDs of each arg"""

    vars = []
    if("args" in tree.keys()):
        for a in tree["args"]:
            names = getNodesOfType(a, "Name")
            for n in names:
                vars.append(n["id"])
    return vars


def getCallID(tree):
    """Given a tree that is a call, returns the name of the function called"""
    
    #Check for calls like a.func()
    atr = getNodesOfType(tree,"Attribute")
    if(atr != []):
        return atr[0]["attr"]
    #Check for calls like func()
    else:
        return tree["func"]["id"]

def getAssignmentCalls(tree):
    """ Given a tree that is an assignment, returns the list of calls (Not considering chained functions) """
        
    # Terrible way to do this, get every named node, get every name that is from a function
    # and return the remaining names
    calls = []

    if(tree["ast_type"] == "Calls"):
        calls.append(tree)
    elif(tree["ast_type"] == "BinOp"):
        calls += getAssignmentCalls(tree["left"]) + getAssignmentCalls(tree["right"])
    elif(tree["ast_type" == "Compare"]):
        for comps in tree["comparators"]:
            calls += getAssignmentCalls(comps) + getAssignmentCalls(tree["left"])
    elif(tree["ast_type"] == "Expr"):
        calls += getAssignmentCalls(tree["value"])
    elif(tree["ast_type"] == "Assignment"):
        for val in tree["value"]:
            calls.append(getAssignmentCalls(val))

    return calls

# ASSIGNMENT FUNCTIONS
        
def getAssignmentTargets(tree):
    """Given a tree that is an assignment, returns a list of IDs of the vars that were assigned"""

    vars = []
    for vt in tree["targets"]:
        targets = getNodesOfType(vt, "Name")
        for t in targets:
            vars.append(t["id"])
    
    return vars

def getAssignmentValues(tree):
    """ Given a tree that is an assignment, returns the list of variable ids used
        in the assignment"""
        
    # Terrible way to do this, get every named node, get every name that is from a function
    # and return the remaining names
    names = []

    if(tree["ast_type"] == "Name"):
        names.append(tree["id"])
    elif(tree["ast_type"] == "BinOp"):
        names += getAssignmentValues(tree["left"]) + getAssignmentValues(tree["right"])
    elif(tree["ast_type" == "Compare"]):
        for comps in tree["comparators"]:
            names += getAssignmentValues(comps) + getAssignmentValues(tree["left"])
    elif(tree["ast_type"] == "Expr"):
        names += getAssignmentValues(tree["value"])
    elif(tree["ast_type"] == "Assignment"):
        for val in tree["value"]:
            names.append(getAssignmentValues(val))

    return names

#def getAssignmentsFromVarWithID(tree, id):
#    """Given a tree and an ID of a variable, returns the list of assignments where
#        the given variable was used as the value of the assignment"""
#    assignments = []
#    assigns = getNodesOfType(tree, "Assign")
#    
#    for a in assigns:
#        if(a["value"]["ast_type"] == "Name" and a["value"]["id"] == id):
#                assignments = assignments + [a]
#    return assignments
#
#def getVarsAssinedAsTargetWithID(tree, id):
#    """Given a tree and an ID of a variable, returns the list of IDs of vars 
#        that where assigned a value of the given variable ID"""
#    assignments = []
#    assigns = getAssignmentsFromVarWithID(tree, id)
#    
#    for a in assigns:
#        for t in a["targets"]:
#            if(t["value"]["ast_type"] == "Name"):
#                    assignments = assignments + [t["value"]["id"] ]
#    return assignments

# COMPARISON FUNCTIONS

def getComparisonIDs(tree):
    """ Given a tree, returns the list of variable ids used
        in the assignment, INCLUDING VARS USED AS FUNCTION ARGS"""
        
    # Terrible way to do this, get every named node, get every name that is from a function
    # and return the remaining names
    names = []
    
    funcCalls = getNodesOfType(tree, "Call")
    funcNames = []
    for c in funcCalls:
        funcNames.append(getCallID(c))
    
    nameNodes = getNodesOfType(tree,"Name")
    for n in nameNodes:
        if(n["id"] not in funcNames and n["id"] not in names):
            names.append(n["id"])
            
    return names