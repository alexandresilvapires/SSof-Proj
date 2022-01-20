# Utils for the various functions of the bo-analyser

# JSON Program utils

from inspect import getcallargs
from ast_utils import *

# Tainted var class holds info about every tainted var

class taintedVars:

    def __init__(self):
        self.vars = {}   # each entry is a tainted var_id, associated with a dict
                    # that holds its info ("sanitized", "sources", "sanitized_flows")
            
    def add_source(self, var_id, source):
        src = source if isinstance(source, list) else [source]
        if "source" in self.vars[var_id]:
            self.vars[var_id]["source"].extend(src)
        else:
            self.vars[var_id]["source"] = src

    def get_source(self, var_id):
        return self.vars[var_id]["source"]

    def set_sanitized(self, var_id, value: bool):
        self.vars[var_id]["sanitized"] = value

    def get_is_sanitized(self, var_id):
        return self.vars[var_id]["sanitized"]

    def add_sanitized_flow(self, var_id, flow):
        flw = flow if isinstance(flow, list) else [flow]
        if "sanitized_flows" in self.vars[var_id]:
            self.vars[var_id]["sanitized_flows"].extend(flw)
        else:
            self.vars[var_id]["sanitized_flows"] = flw

    def get_sanitized_flows(self, var_id):
        return self.vars[var_id]["sanitized_flows"]

    def add_new(self, var_id, sanitized, sources, sanitized_flows):
        self.vars[var_id] = {}
        self.set_sanitized(var_id, sanitized)
        self.add_sanitized_flow(var_id, sanitized_flows)
        self.add_source(var_id, sources)
    
    def get_prop_from_var(self, var_id, fun):
        vars_to_check = [var_id]

        # enquanto nenhuma das variaveis x_i da lista for uma das suas proprias sources
        # entao adicionamos as sources de x_i à lista de variáveis e, se alguma
        # das sources de x_i nao for tainted, retornamos

        while any(x_i not in fun(x_i) for x_i in vars_to_check):
            new_vars = []
            for x in vars_to_check:
                
                for source in fun(x):
                    
                    if source not in self.vars:
                        return source

                new_vars.extend(fun(x))

            vars_to_check = new_vars

        return vars_to_check

    def get_source_from_var(self, var_id):
        """ Given a var ID and the tainted_vars dict, returns the source of the taint recursively """
        return self.get_prop_from_var(var_id, self.get_source)

    def get_all_sanitized_flows_from_var(self, var_id):
        return self.get_prop_from_var(var_id, self.get_sanitized_flows)


def call2dict(call):
    """Turns a funcion call to a easy-to-read dict
    ex: a(b+y,c(d,d),l(t())) = {a:{b_1:None, y_1:None, c_1:{d_1:None,d_2:None},l_1:{t_1:None}}}
    
    Note: Disregards constants."""
    
    f_dict = {}
    
    if(not isinstance(call, dict) or "args" not in call.keys()):
        return f_dict
        
    for arg in call['args']:
        if(arg["ast_type"] == "Name"):
            varName = arg["id"]
            numOcc = 1
            for key in f_dict.keys():
                if(key == varName):
                    numOcc += 1
            f_dict.update({varName+"_"+str(numOcc):{}})
        elif(arg["ast_type"] == "Call"):
            
            varName = getCallID(arg)
            numOcc = 1
            for key in f_dict.keys():
                if(key == varName):
                    numOcc += 1
            f_dict.update({varName+"_"+str(numOcc):call2dict(arg)})
        elif(arg["ast_type"] == 'Expr'):
            f_dict.update(call2dict(arg["value"]))
        elif(arg["ast_type"] == "BinOp"):
            f_dict.update(call2dict(arg["right"]))
            f_dict.update(call2dict(arg["left"]))
        elif(arg["ast_type"] == "Compare"):
            for comps in arg["comparators"]:
                f_dict.update(call2dict(comps))
            f_dict.update(call2dict(arg["left"]))
        
    return f_dict
    
def getCallDictTaint(f_dict, tainted_vars, sources, sanitizers):
    """ Given a function argument dict returns if the function is tainted, and if it is sanitized"""
    isTainted = False
    isSanitized = False
    
    # Cycle each arg and check the combined values of each
    for arg in f_dict.keys():
        # Clean _X from name:
        splits = arg.split("_")
        newArg = ""
        for i in range(0,len(splits)-1):
            newArg += splits[i]
        
        if(newArg in sources or newArg in tainted_vars.vars):
            isTainted = True or isTainted
            
        if(newArg in sanitizers or (newArg in tainted_vars.vars and tainted_vars.get_is_sanitized(newArg))):
            isSanitized = True
        else:
            isSanitized = not isTainted
            
        argTaint, argSanit = getCallDictTaint(f_dict[arg], sources, tainted_vars, sanitizers)
        isTainted = isTainted or argTaint
        isSanitized = isSanitized or (argSanit and not isTainted)
            
    return isTainted, isSanitized and isTainted


def track_taint(tree, entry_points, sanitization, sinks, checkImplicit):
    """ 
    Given a list of entry points, sanitization functions and sinks,
    returns the vunerability, the source, the sink, and if it the source was sanitized.
    Only checks explicit flows.
    """

    # -------------------------- AUXILIARY FUNCTIONS --------------------------

    def update_instantiated_variables(instantiated_vars, target_ids):
        """ 
        Updates the list of instantiated variables taking into account this
        specific loop pass (where a new assignment was analysed).
        """

        instantiated_vars.extend(v for v in target_ids if v not in instantiated_vars)


    def add_tainted_vars_to_dict(tainted_vars, instantiated_vars, var_ids, calls, target_ids):
        """
        Add every target ID to the list of tainted vars, as unsanitized
        and add the uninstantiated vars as tainted too
        """
                    
        def get_sources_sanitflows_from_call(call):
            sources = []
            sanitized_flows = []
            
            callID = getCallID(call)
            
            if(callID in sanitization):
                sanitized_flows.append(callID)
            elif(callID in entry_points):
                sources.append(callID)
                
            argVarIDs = getCallArgVariableIDs(call)
            print(argVarIDs)
            for var in argVarIDs:
                # If id is tainted, add the sources and sanitized flows
                if(var in tainted_vars.vars):
                    sources.extend(tainted_vars.get_source_from_var(var))
                    sanitized_flows.extend(tainted_vars.get_all_sanitized_flows_from_var(var))
                    
                if(var not in instantiated_vars and var not in tainted_vars.vars):
                    print("Uninstantiated var found", var)
                    tainted_vars.add_new(var, False, var, [])
                    sources.append(var)

            for arg in call["args"]:
                # Case for chained functions
                if(arg["ast_type"] == "Call"):
                    
                    # Check chained function args
                    newSources, newSanitFlows = get_sources_sanitflows_from_call(arg)
                    sources.extend(newSources)
                    sanitized_flows.extend(newSanitFlows)
            return sources, sanitized_flows
        
        # Used to know who was the source
        sources = []
        sanitized_flows = []

        for v in var_ids:
        
            # Add uninstantiated vars to the list 
            if v not in instantiated_vars and v not in tainted_vars.vars:
                print("Uninstantiated var found", v)
                tainted_vars.add_new(v, False, v, [])
                sources.append(v)
            # Add sources
            elif v in tainted_vars.vars:
                print("Tainted var found", v)
                sources.extend(tainted_vars.get_source_from_var(v))
                sanitized_flows.extend(tainted_vars.get_all_sanitized_flows_from_var(v))

        for call in calls:
            callID = getCallID(call)

            # check if call is source
            if(callID in sources):
                sources.append(callID)

            # check if it is sanitization
            newSources, newSanitFlows = get_sources_sanitflows_from_call(call)
            sources.extend(newSources)
            sanitized_flows.extend(newSanitFlows)

        # in case any source was found, pass taint to the targets
        print("Sources: ", sources)
        if(sources != []):
            for v in target_ids:
                if v not in tainted_vars.vars:
                    tainted_vars.add_new(v, False, sources, sanitized_flows)
                else:
                    tainted_vars.add_sanitized_flow(v, sanitized_flows)
                    
            # Update the attributed var's sanitization
            attribs = 0
            sanitAttribs = 0
            for var in var_ids:
                attribs += 1
                if(tainted_vars.get_is_sanitized(var)):
                    sanitAttribs += 1
                    
            if(attribs == sanitAttribs):
                for call in calls:
                    attribs += 1
                    _, isSanitized = getCallDictTaint(call2dict(call), tainted_vars, entry_points, sanitization)
                    if(isSanitized):
                        sanitAttribs += 1
            
            for v in target_ids:
                tainted_vars.set_sanitized(v, attribs == sanitAttribs)
            
        # Only constants were assigned, so var is no longer tainted!
        elif(sources == [] and sanitized_flows == []):
            for v in target_ids:
                if(v in tainted_vars.vars):
                    tainted_vars.vars.pop(v)
            

    def get_tainted_sinks(line, tainted_vars, called_ids, target_ids=None):
        """ Gets the sinks that were tainted by this line. """
        def add_tainted_sink_with_id(var_id, sink):
            src = tainted_vars.get_source(var_id)
            is_sanitized = tainted_vars.get_is_sanitized(var_id)
            s_flows = tainted_vars.get_sanitized_flows(var_id)
            print(f"\"{var_id}\"",src, is_sanitized, s_flows)
            ret.append((src, sink, is_sanitized, s_flows))

        def add_tainted_sink(sources, sink, sanitized, s_flows):
            srcs = sources if isinstance(sources, list) else [sources]
            ret.append((srcs, sink, sanitized, s_flows))

        ret = []
        for sink in sinks:
            
            
            
            
            
            # TODO: REFACTOR ALL THIS
            #if sink in called_ids:
            #    call = getCallsWithID(line, sink)
            #    sink_args = []
            #    for c in call:
            #        _, isSanitized = getCallDictTaint(call2dict(call), tainted_vars, entry_points, sanitization)
            #        sink_args += getCallArgsID(c)
            #        
            #        # print(tainted_vars)
            #        # print(function_call_args_to_dict(c))
            #        # print("StatusTime:", getCallDictTaint(call2dict(c), entry_points, tainted_vars, sanitization))
            #
            #    for src in entry_points:
            #        if src in sink_args:
            #            #! SANITIZED FLOWS? TODO
            #            #print(src, "this will have not sanitized flows")
            #            #print(src)
            #            add_tainted_sink(src, sink, False, [])
            #
            #    for t in tainted_vars.vars:
            #        if t in sink_args:
            #            #print("adding",t,"to the list")
            #            add_tainted_sink_with_id(t, sink)
            #
            #elif target_ids and (sink in tainted_vars.vars and sink in target_ids):
            #    add_tainted_sink_with_id(sink, sink)
        
        return ret
        
    def check_for_implicit_flows(line, tainted_vars=[], instantiated_vars=[], tainted_sinks=[]):
        
        # Get every var used in the condition
        varsUsedInCond = getComparisonIDs(line["test"])
        varsUsed = getComparisonIDs(line)

        possiblyImplicit = False
        possibleSources = []
        
        # If a tainted var is used in the comparison, we can consider every following 
        # step that leads to a sink an implicit flow
        
        #for var in varsUsedInCond:
        for var in varsUsedInCond:
            if(var not in instantiated_vars):
                possiblyImplicit = True
                possibleSources.append(var)
            elif(var in tainted_vars.vars):
                possiblyImplicit = True
                possibleSources.append(tainted_vars.get_source_from_var(var))
            # Add every var in cond as a possible source if an implicit flow is possible
            elif((var not in tainted_vars.vars) and possiblyImplicit):
                possibleSources.append(var)

        # If we are considering implicit flows, every variable that interacts with these implicitly tainted vars 
        # must also be considered implicitly tainted
        # So we update the tainted_vars to consider every new implicitly tainted var
        # We also must consider sanitization of these variables
        
        calls = getNodesOfType(line["test"], "Call")
        
        if(possiblyImplicit):

            # check for tainted sources being called
            for call in calls:
                if(getCallID(call) in sinks):
                    possibleSources += getCallID(call)
            
            #for var in varsUsedInCond:
            for var in varsUsed:
                # We dont want flows from a var to the same var #TODO: bad fix for a bad approach
                if([var] == possibleSources):
                    continue

                # Check for sanitization
                for call in calls:
                    fname = getCallID(call)

                    if(fname in sanitization and var in getCallArgsID(call)
                        and (var not in tainted_vars.vars.keys())):
                        tainted_vars.add_new(var, True, possibleSources, [fname])
                    
                # If no sanitization is used
                if(var not in tainted_vars.vars.keys()):
                    tainted_vars.add_new(var, False, possibleSources, [])

    def check_for_tainted_assignments(assignments, tainted_vars, instantiated_vars, tainted_sinks):

        for assignment in assignments:
            calls = getAssignmentCalls(assignment)
            
            """ List of variable ids that were used on the right side of the assignment """
            var_ids = getAssignmentValues(assignment)
            
            print("Var ids:", var_ids)

            """ List of target variables, used on the left side of the assignment """
            target_ids = getAssignmentTargets(assignment)

            add_tainted_vars_to_dict(tainted_vars, instantiated_vars, var_ids, calls, target_ids)
            
            update_instantiated_variables(instantiated_vars, target_ids)

            called_ids = [getCallID(c) for c in calls] #TODO: ADDED JUST TO WORK ATM
            tainted_sinks.extend(get_tainted_sinks(line, tainted_vars, called_ids, target_ids))
    
    def check_for_lonely_call_tainting(line, tainted_vars, tainted_sinks):
        lonely_calls = getNodesOfType(line, "Call")
        called_ids = [getCallID(call) for call in lonely_calls]
        tainted_sinks.extend(get_tainted_sinks(line, tainted_vars=tainted_vars, called_ids=called_ids))

    # ----------------------------- MAIN FUNCTION -----------------------------

    """
    Dictionary with tainted vars. Each var is associated with a dict, which has:
        - a bool ("sanitized") where it is true if the var has been sanitized
        - a string ("source") with the source id, that is, the variable that tainted it 
              (if this variable has another source, it gets this value instead, recursively) 
              If the var is not initialized, or the taint comes from a entry point,
              the source is its own ID
    """
    tainted_vars = taintedVars()
    
    """
    Keeps track of instantiated variables, since by default uninstantiated vars
    are to be considered vunerable
    """
    instantiated_vars = []

    tainted_sinks = []

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
            if(calls != []):
                check_for_lonely_call_tainting(line, tainted_vars=tainted_vars, tainted_sinks=tainted_sinks)
        
        print(tainted_vars.vars)
        
    return tainted_sinks
