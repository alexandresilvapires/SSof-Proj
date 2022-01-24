import copy
from mailbox import linesep

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

    if(tree["ast_type"] == "Call"):
        calls.append(tree)
    elif(tree["ast_type"] == "BinOp"):
        calls += getAssignmentCalls(tree["left"]) + getAssignmentCalls(tree["right"])
    elif(tree["ast_type"] == "Compare"):
        for comps in tree["comparators"]:
            calls += getAssignmentCalls(comps) + getAssignmentCalls(tree["left"])
    elif(tree["ast_type"] == "Expr"):
        calls += getAssignmentCalls(tree["value"])
    elif(tree["ast_type"] == "Assign"):
        calls += getAssignmentCalls(tree["value"])

    return calls

def getCallArgVariableIDs(tree):
    """ Given a tree that is a call, returns the list of variable arguments """
        
    # Terrible way to do this, get every named node, get every name that is from a function
    # and return the remaining names
    vars = []

    if(tree["ast_type"] == "BinOp"):
        vars += getCallArgVariableIDs(tree["left"]) + getCallArgVariableIDs(tree["right"])
    elif(tree["ast_type"] == "Compare"):
        for comps in tree["comparators"]:
            vars += getCallArgVariableIDs(comps) + getCallArgVariableIDs(tree["left"])
    elif(tree["ast_type"] == "Expr"):
        vars += getCallArgVariableIDs(tree["value"])
    elif(tree["ast_type"] == "Assign"):
        vars += getCallArgVariableIDs(tree["value"])
    elif(tree["ast_type"] == "Call"):
        for arg in tree["args"]:
            vars += getCallArgVariableIDs(arg)
    elif(tree["ast_type"] == "Name"):
        vars.append(tree["id"])

    return vars

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
        
    names = []

    if(tree["ast_type"] == "Name"):
        names.append(tree["id"])
    elif(tree["ast_type"] == "BinOp"):
        names += getAssignmentValues(tree["left"]) + getAssignmentValues(tree["right"])
    elif(tree["ast_type"] == "Compare"):
        for comps in tree["comparators"]:
            names += getAssignmentValues(comps) + getAssignmentValues(tree["left"])
    elif(tree["ast_type"] == "Expr"):
        names += getAssignmentValues(tree["value"])
    elif(tree["ast_type"] == "Assign"):
        names += getAssignmentValues(tree["value"])

    return names

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

# TREE CONDITIONAL HANDELING

def popLineFromTree(tree, line):
    
    def popLineFromTreeAux(tree, line):
        # see conditionals
        for i in range(0, len(tree["body"])):
            if(tree["body"][i] == line):
                return True, i, tree
            elif(tree["body"][i]["ast_type"] == "If"):
                inIf, newI, _ = popLineFromTreeAux(tree["body"][i], line)
                inElse, newI, _ = popLineFromTreeAux(tree["orelse"][i], line)
                if(inIf):
                    tree["body"][i]["body"].pop(newI)
                    return True, newI, tree
                elif(inElse):
                    tree["body"][i]["orelse"].pop(newI)
                    return True, newI, tree
            elif(tree["body"][i]["ast_type"] == "While"):
                inWhile, newI, _ = popLineFromTreeAux(tree["body"][i], line)
                if(inWhile):
                    tree["body"][i]["body"].pop(newI)
                    return True, newI, tree
                    
        return False, -1, tree
    _, _, newTree = popLineFromTreeAux(tree, line)
    return newTree

def getAllTrees(tree):
    trees = []
    
    for i in range(0, len(getLines(tree))):
        # If we have an if, we want to make a version with only the if and one with only the else
        if(tree["body"][i]["ast_type"] == "If"):
            # A version without the else turns the else body into empty
            withIf = copy.deepcopy(tree)
            
            withIf["body"][i]["orselse"] = []
            
            # Check for recursive ifs 
            newIfBodies = getAllTrees(withIf["body"][i])
            for new in newIfBodies:
                newTree = copy.deepcopy(withIf)
                newTree["body"][i]["body"] = new
                trees.append(newTree)
            if(newIfBodies == []):
                trees.append(withIf)
                
            
            # A version without the if keeps the condition for implicit flow tracking but replaces
            # the if body with the else body, and removes the other else body
            withElse = copy.deepcopy(tree)
            
            withElse["body"][i]["body"] = withElse["body"][i]["orelse"]
            withElse["body"][i]["orelse"] = []
            
            # Check for recursive ifs 
            newIfBodies = getAllTrees(withElse["body"][i])
            for new in newIfBodies:
                newTree = copy.deepcopy(withIf)
                newTree["body"][i]["body"] = new
                trees.append(newTree)
            if(newIfBodies == []):
                trees.append(withIf)
            trees.append(withElse)
            
        # If we have a while, we duplicate the body to unroll the loop and check all the subtrees the body can have
        elif(tree["body"][i]["ast_type"] == "While"):
            withWhile = copy.deepcopy(tree)
            
            # Unroll the loop
            newLines = getLines(tree["body"][i]) + getLines(tree["body"][i])
            withWhile["body"][i]["body"] = newLines
            
            subtrees = getAllTrees(withWhile["body"][i])
            for st in subtrees:
                newTree = copy.deepcopy(withWhile)
                newTree["body"][i]["body"] = st
                trees.append(st)
            
            if(subtrees == []):
                trees.append(withWhile)
                
            # add subtree without while
            newTree = copy.deepcopy(tree)
            newTree = popLineFromTree(tree, tree["body"][i])
            trees.append(newTree)

    if(trees == []):
        return [tree]
    else:
        return trees