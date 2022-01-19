# Utils for the various functions of the bo-analyser

# JSON Program utils

from cmath import sin
from unittest import skip

from numpy import var


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

def getVarsUsedAsValueComparisons(tree):
    """ Given a tree, returns the list of variable ids used
        in the assignment, INCLUDING VARS USED AS FUNCTION ARGS"""
        
    # Terrible way to do this, get every named node, get every name that is from a function
    # and return the remaining names
    names = []
    
    funcCalls = getNodesOfType(tree, "Call")
    funcNames = []
    for c in funcCalls:
        funcNames.append(getFunctionNameFromCall(c))
    
    nameNodes = getNodesOfType(tree,"Name")
    for n in nameNodes:
        if(n["id"] not in funcNames and n["id"] not in names):
            names.append(n["id"])
            
    return names

def removeDupesFromList(l):
    return list(set(l))


def track_taint(tree, entry_points, sanitization, sinks, checkImplicit):
    """ 
    Given a list of entry points, sanitization functions and sinks,
    returns the vunerability, the source, the sink, and if it the source was sanitized.
    Only checks explicit flows.
    """

    # -------------------------- AUXILIARY FUNCTIONS --------------------------

    def set_sanitized_tainted_var(tainted_vars, var_id, value: bool):
        tainted_vars[var_id]["sanitized"] = value

    def add_source_to_tainted_var(tainted_vars, var_id, source):
        src = source if isinstance(source, list) else [source]
        if "source" in tainted_vars[var_id]:
            tainted_vars[var_id]["source"].extend(src)
        else:
            tainted_vars[var_id]["source"] = src

    def add_sanitized_flow_tainted_var(tainted_vars, var_id, flow):
        flw = flow if isinstance(flow, list) else [flow]
        if "sanitized_flows" in tainted_vars[var_id]:
            tainted_vars[var_id]["sanitized_flows"].extend(flw)
        else:
            tainted_vars[var_id]["sanitized_flows"] = flw

    def add_new_tainted_var(tainted_vars, var_id, sanitized, sources, sanitized_flows):
        tainted_vars[var_id] = {}
        set_sanitized_tainted_var(tainted_vars, var_id, sanitized)
        add_sanitized_flow_tainted_var(tainted_vars, var_id, sanitized_flows)
        add_source_to_tainted_var(tainted_vars, var_id, sources)

    def get_is_sanitized_tainted_var(tainted_vars, var_id):
        return tainted_vars[var_id]["sanitized"]

    def get_source_tainted_var(tainted_vars, var_id):
        return tainted_vars[var_id]["source"]

    def get_sanitized_flows_tainted_var(tainted_vars, var_id):
        return tainted_vars[var_id]["sanitized_flows"]

    def get_prop_from_var(tainted_vars, var_id, fun):
        vars_to_check = [var_id]

        # enquanto nenhuma das variaveis x_i da lista for uma das suas proprias sources
        # entao adicionamos as sources de x_i à lista de variáveis e, se alguma
        # das sources de x_i nao for tainted, retornamos

        while any(x_i not in fun(tainted_vars, x_i) for x_i in vars_to_check):
            new_vars = []
            for x in vars_to_check:
                
                for source in fun(tainted_vars, x):
                    
                    if source not in tainted_vars:
                        return source

                new_vars.extend(fun(tainted_vars, x))

            vars_to_check = new_vars

        return vars_to_check

    def get_source_from_var(tainted_vars, var_id):
        """ Given a var ID and the tainted_vars dict, returns the source of the taint recursively """
        return get_prop_from_var(tainted_vars, var_id, get_source_tainted_var)

    def get_all_sanitized_flows_from_var(tainted_vars, var_id):
        return get_prop_from_var(tainted_vars, var_id, get_sanitized_flows_tainted_var)

    def check_sanitization(calls, var_ids, tainted_vars, tainted_count):
        """
        For every call made, if the arg was tainted, set sanitized bool to true
        and lower tainted int, so if tainted == 0 in the end, we can assume only sanitized functions were given
        """
        def var_not_sanitized(var):
            return var in tainted_vars and not get_is_sanitized_tainted_var(tainted_vars, var)

        start_tc = tainted_count
        for c in calls:
            func_name = getFunctionNameFromCall(c)
            if func_name in sanitization:
                for var in var_ids:
                    if var in getArgsIDFromCall(c) and var_not_sanitized(var):
                        tainted_count -= 1
        
        is_sanitized = start_tc != tainted_count

        return is_sanitized, tainted_count

    def add_tainted_vars_to_dict(tainted_vars, instantiated_vars, var_ids, called_ids, target_ids):
        """
        Add every target ID to the list of tainted vars, as unsanitized
        and add the uninstantiated vars as tainted too
        """
        def add_call_sources_to_var(var_id):
            for call in called_ids:
                if call in entry_points:
                    add_source_to_tainted_var(tainted_vars, var_id, call)
                elif call in sanitization:
                    add_sanitized_flow_tainted_var(tainted_vars, var_id, call)

        # Used to know who was the source
        sources = []
        sanitized_flows = []

        # Add uninstantiated vars to the list 
        for v in var_ids:
            if v not in instantiated_vars and v not in tainted_vars:
                add_new_tainted_var(tainted_vars, v, False, v, [])
                sources.append(v)
            elif v in tainted_vars:
                if v in entry_points:
                    sources.append(v)
                sources.extend(get_source_from_var(tainted_vars, v))
                sanitized_flows.extend(get_all_sanitized_flows_from_var(tainted_vars, v))

        for v in target_ids:
            if v not in tainted_vars:
                add_new_tainted_var(tainted_vars, v, False, sources, sanitized_flows)
            else:
                add_sanitized_flow_tainted_var(tainted_vars, v, sanitized_flows)
            add_call_sources_to_var(v)
            

    def update_tainted_values(assignment, tainted_vars, target_ids, is_sanitized, called_ids):
        if is_sanitized:
            # If anything is sanitized, and no taints were made (tainted == 0),
            # then the variables were totally sanitized, 
            # so every target ID's sanitization value is set to true
            called_sanitizations = list(set(called_ids) & set(sanitization))
            for v in target_ids:
                sources = []
                for c_id in called_ids:
                    args = []
                    call = getCallsWithID(assignment, c_id)
                    for c in call:
                        args += getArgsIDFromCall(c)
                        sources.extend(get_source_from_var(tainted_vars, args[-1]))
                
                if v in tainted_vars:
                    set_sanitized_tainted_var(tainted_vars, v, True)
                    add_source_to_tainted_var(tainted_vars, v, sources)
                    add_sanitized_flow_tainted_var(tainted_vars, v, called_sanitizations)
                else:
                    add_new_tainted_var(tainted_vars, v, True, sources, called_sanitizations)
        else:
            # Every target ID is now clean, as the value attributed is totally clean
            for value in target_ids:
                if value in tainted_vars:
                    tainted_vars.pop(value)

    def add_tainted_sink(tainted_sinks, sink, sources, is_sanitized, s_flows):
        def add_s_flows_and_set_sanitized():
            for src in sources:
                current_s_flows = tainted_sinks[sink]["sanitized_flows"]

                if src in current_s_flows:
                    current_s_flows[src].extend(s_flows)
                else:
                    current_s_flows[src] = s_flows.copy()

                #! Update rule needs reviewing!!!!!!!
                tainted_sinks[sink]["is_sanitized"][src] = is_sanitized

        #! needs to be refactored and create abstract data type
        if sink in tainted_sinks:
            current_sources = tainted_sinks[sink]["source"]
            tainted_sinks[sink]["source"].extend([src for src in sources if src not in current_sources])
            
            add_s_flows_and_set_sanitized()

        else:
            tainted_sinks[sink] = {}
            tainted_sinks[sink]["source"] = sources.copy()
            tainted_sinks[sink]["is_sanitized"] = {}
            tainted_sinks[sink]["sanitized_flows"] = {}

            add_s_flows_and_set_sanitized()
            
    def update_tainted_sinks(line, tainted_vars, called_ids, target_ids=None):
        """ Gets the sinks that were tainted by this line. """

        def add_tainted_sink_with_id(var_id, sink):
            src = get_source_tainted_var(tainted_vars, var_id)
            is_sanitized = get_is_sanitized_tainted_var(tainted_vars, var_id)
            s_flows = get_sanitized_flows_tainted_var(tainted_vars, var_id)

            add_tainted_sink(tainted_sinks, sink, src, is_sanitized, s_flows)

        def add_tainted_sink_w_props(sources, sink, sanitized, s_flows):
            srcs = sources if isinstance(sources, list) else [sources]
            add_tainted_sink(tainted_sinks, sink, srcs, sanitized, s_flows)

        for sink in sinks:
            if sink in called_ids:
                call = getCallsWithID(line, sink)

                sink_args = []
                for c in call:
                    sink_args += getArgsIDFromCall(c)

                for src in entry_points:
                    if src in sink_args:
                        #! SANITIZED FLOWS?
                        add_tainted_sink_w_props(src, sink, False, [])

                for t in tainted_vars:
                    if t in sink_args:
                        add_tainted_sink_with_id(t, sink)

            elif target_ids and (sink in tainted_vars and sink in target_ids):
                add_tainted_sink_with_id(sink, sink)

    def update_instantiated_variables(instantiated_vars, target_ids):
        """ 
        Updates the list of instantiated variables taking into account this
        specific loop pass (where a new assignment was analysed).
        """

        instantiated_vars.extend(v for v in target_ids if v not in instantiated_vars)
        
    def check_for_implicit_flows(line, tainted_vars=[], instantiated_vars=[], tainted_sinks=[]):
        
        # Get every var used in the condition
        varsUsedInCond = getVarsUsedAsValueComparisons(line["test"])
        varsUsed = getVarsUsedAsValueComparisons(line)

        possiblyImplicit = False
        possibleSources = []
        
        # If a tainted var is used in the comparison, we can consider every following 
        # step that leads to a sink an implicit flow
        
        #for var in varsUsedInCond:
        for var in varsUsedInCond:
            if(var not in instantiated_vars):
                possiblyImplicit = True
                possibleSources.append(var)
            elif(var in tainted_vars):
                possiblyImplicit = True
                possibleSources.append(get_source_from_var(tainted_vars, var))
            # Add every var in cond as a possible source if an implicit flow is possible
            elif((var not in tainted_vars) and possiblyImplicit):
                possibleSources.append(var)

        # If we are considering implicit flows, every variable that interacts with these implicitly tainted vars 
        # must also be considered implicitly tainted
        # So we update the tainted_vars to consider every new implicitly tainted var
        # We also must consider sanitization of these variables
        
        calls = getNodesOfType(line["test"], "Call")
        
        if(possiblyImplicit):

            # check for tainted sources being called
            for call in calls:
                if(getFunctionNameFromCall(call) in sinks):
                    possibleSources += getFunctionNameFromCall(call)
            
            #for var in varsUsedInCond:
            for var in varsUsed:
                # We dont want flows from a var to the same var #TODO: bad fix for a bad approach
                if([var] == possibleSources):
                    continue

                # Check for sanitization
                for call in calls:
                    fname = getFunctionNameFromCall(call)

                    if(fname in sanitization and var in getArgsIDFromCall(call)
                        and (var not in tainted_vars.keys())):
                        if(var not in instantiated_vars):
                            tainted_vars[var] = {"source":possibleSources, "sanitized": True, "sanitized_flows":[fname]}
                        else:
                            tainted_vars[var] = {"source":possibleSources, "sanitized": True, "sanitized_flows":[fname]}
                    
                # If no sanitization is used
                if(var not in tainted_vars.keys()):
                    if(var not in instantiated_vars):
                        tainted_vars[var] = {"source":possibleSources, "sanitized": False, "sanitized_flows":[]}
                    else:
                        tainted_vars[var] = {"source":possibleSources, "sanitized": False,"sanitized_flows":[]}

    def check_for_tainted_assignments(assignments, tainted_vars, instantiated_vars, tainted_sinks):

        #TODO: CHECK FOR CHAINED FUNCTIONS

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
                add_tainted_vars_to_dict(tainted_vars, instantiated_vars, var_ids, called_ids, target_ids)
            else:
                update_tainted_values(assignment, tainted_vars, target_ids, is_sanitized, called_ids)
                            
            update_instantiated_variables(instantiated_vars, target_ids)

            update_tainted_sinks(line, tainted_vars, called_ids, target_ids)
    
    def check_for_lonely_call_tainting(line, tainted_vars):
        lonely_calls = getNodesOfType(line, "Call")
        called_ids = [getFunctionNameFromCall(call) for call in lonely_calls]
        update_tainted_sinks(line, tainted_vars=tainted_vars, called_ids=called_ids)

    # ----------------------------- MAIN FUNCTION -----------------------------

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

    tainted_sinks = {}

    for line in getLines(tree):
        
        # check implicit flows if conditionals exist
        if(checkImplicit):
            if(line["ast_type"] == "If" or line["ast_type"] == "While"):
                check_for_implicit_flows(line, tainted_vars=tainted_vars, instantiated_vars=instantiated_vars, tainted_sinks=tainted_sinks)
        
        # Also check for explicit flows
        assignments = getNodesOfType(line, "Assign")

        if assignments != []:
            check_for_tainted_assignments(assignments, tainted_vars=tainted_vars, instantiated_vars=instantiated_vars, tainted_sinks=tainted_sinks)
            
        else:
            calls = getNodesOfType(line, "Call")
            if calls != []:
                check_for_lonely_call_tainting(line, tainted_vars=tainted_vars)
    return tainted_sinks

def get_source_from_vuln(vuln):
    return vuln["source"]

def get_is_sanitized_from_vuln(vuln, src):
    return vuln["is_sanitized"][src]

def get_sanitized_flows_from_vuln(vuln, src):
    return vuln["sanitized_flows"][src]