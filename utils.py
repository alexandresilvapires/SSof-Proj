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


def track_taint(tree, entry_points, sanitization, sinks):
    """ 
    Given a list of entry points, sanitization functions and sinks,
    returns the vunerability, the source, the sink, and if it the source was sanitized.
    Only checks explicit flows.
    """

    # -------------------------- AUXILIARY FUNCTIONS --------------------------

    def getSourceFromVar(tainted_vars, varID):
        """ Given a var ID and the tainted_vars dict, returns the source of the taint recursively"""
        curvar = varID
        while(tainted_vars[curvar]["source"] != curvar):
            curvar = tainted_vars[curvar]["source"]

            # Case for uninitialized vars
            if(curvar not in tainted_vars.keys()):
                return curvar
        return curvar

    def check_sanitization(calls, var_ids, tainted_vars, tainted_count):
        """
        For every call made, if the arg was tainted, set sanitized bool to true
        and lower tainted int, so if tainted == 0 in the end, we can assume only sanitized functions were given
        """
        def var_not_sanitized(var):
            return var in tainted_vars.keys() and tainted_vars[v]["sanitized"] == False

        start_tc = tainted_count
        is_sanitized = False
        for c in calls:
            func_name = getFunctionNameFromCall(c)
            if func_name in sanitization:
                for var in var_ids:
                    if var in getArgsIDFromCall(c) and var_not_sanitized(var):
                        tainted_count -= 1
        
        is_sanitized = start_tc != tainted_count

        return is_sanitized, tainted_count

    def add_tainted_vars_to_dict(tainted_vars, var_ids, instantiated_vars, target_ids):
        """
        Add every target ID to the list of tainted vars, as unsanitized
        and add the uninstantiated vars as tainted too
        """

        #! THIS FUNCTION IS VERY WRONG. taintedVarForSource changes independently
        #! from the other variables being considered.

        # Used to know who was the source
        taintedVarForSource = None

        # Add uninstantiated vars to the list 
        for v in var_ids:
            if v not in instantiated_vars and v not in tainted_vars.keys():
                    tainted_vars[v] = {"sanitized":False, "source": v}
            if v in tainted_vars.keys():
                taintedVarForSource = v

        #Search for entry points to consider the source
        for c in called_ids:
            if c in entry_points:
                taintedVarForSource = c
        
        if taintedVarForSource:
            taintedVarForSource = getSourceFromVar(tainted_vars, taintedVarForSource)

        for v in target_ids:
            if v not in tainted_vars.keys():
                tainted_vars[v] = {"sanitized": False, "source": taintedVarForSource}

    def update_tainted_values(tainted_vars, target_ids, is_sanitized):
        if is_sanitized:
            # If anything is sanitized, and no taints were made (tainted == 0),
            # then the variables were totally sanitized, 
            # so every target ID's sanitization value is set to true
            for v in target_ids:
                tainted_vars[v]["sanitized"] = True
        else:
            # Every target ID is now clean, as the value attributed is totally clean
            for value in target_ids:
                if value in tainted_vars:
                    tainted_vars.pop(value)

    def get_tainted_sinks(assignment, tainted_vars, called_ids):
        """ Gets the sinks that were tainted by this assignment. """
        ret = []
        for sink in sinks:
            if sink in called_ids:
                call = getCallsWithID(assignment, sink)
                sink_args = []

                # can call the sink more than once!
                for c in call:
                    sink_args += getArgsIDFromCall(c)
                for t in tainted_vars.keys():
                    if t in sink_args:
                        ret.append((tainted_vars[t]["source"], sink, tainted_vars[t]["sanitized"]))
        return ret

    def update_instantiated_variables(instantiated_vars, target_ids):
        """ 
        Updates the list of instantiated variables taking into account this
        specific loop pass (where a new assignment was analysed).
        """

        instantiated_vars.extend(v for v in target_ids if v not in instantiated_vars)

    # ----------------------------- MAIN FUNCTION -----------------------------

    assignments = getNodesOfType(tree, "Assign")

    """
    Dictionary with tainted vars. Each var is associated with a dict, which has:
        - a bool ("sanitized") where it is true if the var has been sanitized
        - a string ("source") with the source id, that is, the variable that tainted it 
              (if this variable has another source, it gets this value instead, recursively) 
              If the var is not initialized, or the taint comes from a entry point,
              the source is its own ID
    """
    tainted_vars = {}
    
    """
    Keeps track of instantiated variables, since by default uninstantiated vars
    are to be considered vunerable
    """
    instantiated_vars = []

    tainted_sinks = []

    #TODO: CHECK FOR CHAINED FUNCTIONS
    #      Check sink outside assignments
    #           eg: sink(a) 
    #      Return all possible vuns, not just the first found
    #      Add sanitized flows (list of sanitization functions used)
    for assignment in assignments:
        """
        Counts every time an entry point or tainted variable is used in 
        an assignment.
        """
        tainted_count = 0   

        calls = getNodesOfType(assignment, "Call")

        """ List of function names that were called in the assignment """
        called_ids = [getFunctionNameFromCall(c) for c in calls]
        
        """ List of variable ids that were used on the right side of the assignment """
        var_ids = getVarsUsedAsValue(assignment)

        """ List of target variables, used on the left side of the assignment """
        target_ids = getTargetIDInAssignment(assignment)

        """Sum of variables where an assignment was an entry point"""
        tainted_count += sum(1 for e in entry_points if e in called_ids)

        """Sum of variables that were assigned the value of a tainted var (even if as an arg)"""
        tainted_count += sum(1 for v in var_ids if v in tainted_vars or v not in instantiated_vars)
                
        is_sanitized, tainted_count = check_sanitization(calls, var_ids, tainted_vars, tainted_count)
        
        if tainted_count > 0:
            add_tainted_vars_to_dict(tainted_vars, var_ids, instantiated_vars, target_ids)
        else:
            update_tainted_values(tainted_vars, target_ids, is_sanitized)
                        
        update_instantiated_variables(instantiated_vars, target_ids)

        tainted_sinks.extend(get_tainted_sinks(assignment, tainted_vars, called_ids))

    return tainted_sinks
