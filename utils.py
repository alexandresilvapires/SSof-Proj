# Utils for the various functions of the bo-analyser

# JSON Program utils

from inspect import getcallargs
from sre_constants import CALL
from ast_utils import *

# Tainted var class holds info about every tainted var

class taintedVars:

    def __init__(self):
        self.vars = {}   # each entry is a tainted var_id, associated with a dict
                    # that holds its info {"sanitized":False, "sources":{"source1":[sanitflow],"source2":[sanitflow]}}
            
    def add_source(self, var_id, source):
        if "sources" in self.vars[var_id]:
            self.vars[var_id]["sources"].update({source:[]})
        else:
            self.vars[var_id]["sources"] = {source:[]}

    def get_sources(self, var_id):
        return self.vars[var_id]["sources"]

    def set_sanitized(self, var_id, value: bool):
        self.vars[var_id]["sanitized"] = value

    def get_is_sanitized(self, var_id):
        return self.vars[var_id]["sanitized"]

    def add_sanitized_flow(self, var_id, source, flow):
        flw = flow if isinstance(flow, list) else [flow]
        if(not "sources" in self.vars[var_id] or not source in self.vars[var_id]["sources"]):
            self.add_source(var_id, source)
        self.vars[var_id]["sources"][source].extend(flw)
        
        self.vars[var_id]["sources"][source] = list(dict.fromkeys(self.vars[var_id]["sources"][source]))
        
        

    def get_sanitized_flows(self, var_id, source):
        return self.vars[var_id]["sources"][source]

    def add_new(self, var_id, sanitized, source_flows):
        self.vars[var_id] = {}
        self.vars[var_id]["sources"] = {}
        self.set_sanitized(var_id, sanitized)
        for var in source_flows:
            self.add_source(var_id, var)
            self.add_sanitized_flow(var_id, var, source_flows[var])
            
    
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
        return self.get_prop_from_var(var_id, self.get_sources)

    def get_all_sources_from_var(self, var_id):
        """ Given a var ID and the tainted_vars dict, returns the source of the taint recursively """
        return list(self.vars[var_id]["sources"].keys())



    def get_all_sanitized_flows_from_var(self, var_id):
        sources = self.get_sources(var_id)
        sanit = []
        for s in sources:
            sanit.extend(self.get_sanitized_flows(var_id, s))
        return sanit
        #return self.get_prop_from_var(var_id, self.get_sanitized_flows)


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
            
        argTaint, argSanit = getCallDictTaint(f_dict[arg], tainted_vars, sources, sanitizers)
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

    def get_sources_sanitflows_from_call(call, tainted_vars, instantiated_vars, tainted_sinks):
        
        sources_flows = {}
        
        callID = getCallID(call)
        
        if callID in entry_points:
            sources_flows[callID] = []


        argVarIDs = getCallArgVariableIDs(call)
        for var in argVarIDs:
            # If id is tainted, add the sources and sanitized flows
            if var in tainted_vars.vars:
                s = tainted_vars.get_all_sources_from_var(var)
                sf = tainted_vars.get_all_sanitized_flows_from_var(var)

                # If the current function is a sanitization function, add it to the sanitized flows
                if callID in sanitization:
                    sf.append(callID)
                elif callID in sinks:
                    #* Big messy boiii
                    is_sanitized = tainted_vars.get_is_sanitized(var)
                    srcs = tainted_vars.get_sources(var)
                    if callID in tainted_sinks:
                        for src in srcs:
                            if src not in tainted_sinks[callID]["source"]:
                                tainted_sinks[callID]["source"].update({src: srcs[src]})
                            else:
                                for flow in srcs[src]:
                                    if flow not in tainted_sinks[callID]["source"][src]:
                                        tainted_sinks[callID]["source"][src].append(flow)

                        # The sink remains sanitized if the sources appended were sanitized as well. Otherwise, it is not sanitized no more.
                        #! This is slightly wrong.
                        tainted_sinks[callID]["is_sanitized"] = tainted_sinks[callID]["is_sanitized"] and is_sanitized
                    else:
                        #! Might need to add these elsewhere, too
                        #s_flows_to_add = []
                        #for src in srcs:
                        #    for s_flow in srcs[src]:
                        #        if s_flow not in s_flows_to_add:
                        #            s_flows_to_add.append(s_flow)

                        # TODO: was {var: s_flows_to_add}, but 'srcs' is correct?
                        print("---sources", srcs)
                        tainted_sinks[callID] = {
                                                "source": srcs,
                                                "is_sanitized": is_sanitized
                                                }
                    
                for source in s:
                    #? Não sei se isto é necessariamente verdade.
                    #? Estamos a dizer que todas as sources da variável têm os mesmos
                    #? Sanitized flows!
                    sources_flows[source] = sf
                
            # if var is uninstantiated, add it to the found vars
            elif (var not in instantiated_vars and var not in tainted_vars.vars):
                
                # If the current function is a sanitization function, add it to the sanitized flows
                if(callID in sanitization):
                    tainted_vars.add_new(var, True, {var:[callID]})
                    sources_flows[var] = [callID]
                else:
                    tainted_vars.add_new(var, False, {var:[]})
                    sources_flows[var] = []

                if callID in sinks:
                    if callID in tainted_sinks:
                        if var not in tainted_sinks[callID]["source"]:
                            tainted_sinks[callID]["source"].update({var: sources_flows[var]})
                        else:
                            for flow in sources_flows[var]:
                                if flow not in tainted_sinks[callID]["source"][var]:
                                    tainted_sinks[callID]["source"][var].append(flow)
                    else:
                        tainted_sinks[callID] = {
                                                "source": {var: sources_flows[var]},
                                                }
                    
                    tainted_sinks[callID]["is_sanitized"] = sources_flows[var] != []
        
        for arg in call["args"]:
            # Case for chained functions
            if arg["ast_type"] == "Call":
                # Check chained function args
                arg_sources_flows = get_sources_sanitflows_from_call(arg,
                                                                    tainted_vars,
                                                                    instantiated_vars,
                                                                    tainted_sinks)

                for src in arg_sources_flows:
                    sources_flows.update({src: arg_sources_flows[src].copy()})

                # Update the tainted sinks
                for var in arg_sources_flows:
                    if callID in sinks:
                        if callID in tainted_sinks:
                            if var not in tainted_sinks[callID]["source"]:
                                tainted_sinks[callID]["source"].update({var: arg_sources_flows[var].copy()})
                            else:
                                for flow in sources_flows[var]:
                                    if flow not in tainted_sinks[callID]["source"][var]:
                                        tainted_sinks[callID]["source"][var].append(flow)
                        else:
                            tainted_sinks[callID] = {
                                                    "source": {var: arg_sources_flows[var].copy()},
                                                    }
                        
                        tainted_sinks[callID]["is_sanitized"] = sources_flows[var] != []


                # Add this sanitization function to the flows
                if callID in sanitization:
                    for src in arg_sources_flows:
                        arg_sources_flows[src].append(callID)
                        sources_flows.update({src: arg_sources_flows[src].copy()})

        return sources_flows

    def add_tainted_vars_to_dict(tainted_vars, instantiated_vars, var_ids, calls, target_ids, tainted_sinks,clean):
        """
        Add every target ID to the list of tainted vars, as unsanitized
        and add the uninstantiated vars as tainted too
        """
        
        sanitized_flows_source = {}

        # Update unitialized vars in case only constants are being assigned
        if(var_ids == [] and calls == []):
            for var in target_ids:
                if(var not in instantiated_vars):
                    instantiated_vars.append(var)

        # Check if any entry points are being assigned
        for v in target_ids:
            if(v in entry_points):
                tainted_vars.add_new(v, False, {v:[]})
                sanitized_flows_source[v] = []

        # Track sources and their sanitized flows for both vars and calls in assigned value
        
        for v in var_ids:
            # Add uninstantiated vars to the list 
            if v not in instantiated_vars and v not in tainted_vars.vars:
                print("Uninstantiated var found", v)
                tainted_vars.add_new(v, False, {v:[]})
                sanitized_flows_source[v] = []
            # Add tainted vars
            elif v in tainted_vars.vars:
                print("Tainted var found", v)
                s = tainted_vars.get_all_sources_from_var(v)
                sf = tainted_vars.get_all_sanitized_flows_from_var(v)
                for source in s:
                    sanitized_flows_source[source] = sf
                
            if v in entry_points:
                if v not in tainted_vars.vars:
                    tainted_vars.add_new(v, False, {v:[]})
                    sanitized_flows_source[v] = []

        for call in calls:
            callID = getCallID(call)

            # check if call is entry point
            if(callID in entry_points):
                sanitized_flows_source[callID] = []

            # check if it is sanitization
            sanitized_flows_source.update(get_sources_sanitflows_from_call(call, tainted_vars, instantiated_vars, tainted_sinks))

        # in case any source was found, pass taint to the targets
        if sanitized_flows_source != {}:
            for v in target_ids:
                if v not in tainted_vars.vars:
                    tainted_vars.add_new(v, False, sanitized_flows_source)
                else:
                    for s in sanitized_flows_source:
                        tainted_vars.add_sanitized_flow(v, s, sanitized_flows_source[s])
                
                if v in entry_points:
                    tainted_vars.add_source(v, v)
                        
            # Update the attributed var's sanitization
            attribSanitization = 0  # Var or call being attributed increases the counter
                                    # If the var or call is sanitized, the counter decreases.
                                    # An assignment target is sanitized if everything is also sanitized
            for var in var_ids:
                attribSanitization += 1
                if(tainted_vars.get_is_sanitized(var)):
                    attribSanitization -= 1
    
            # We only verify calls if everything is sanitized for now
            if attribSanitization == 0:
                for call in calls:
                    attribSanitization += 1
                    _, isSanitized = getCallDictTaint(call2dict(call), tainted_vars, entry_points, sanitization)
                    if(isSanitized or callID in sanitization):
                        attribSanitization -= 1
            
            # Update the sanitization value
            for v in target_ids:
                tainted_vars.set_sanitized(v, attribSanitization == 0)
                if v in sinks:
                    if v in tainted_sinks:
                        srcs = tainted_vars.get_sources(v)
                        for src in srcs:
                            if src not in tainted_sinks[v]["source"]:
                                tainted_sinks[v]["source"].update({src: srcs[src]})
                            else:
                                for flow in srcs[src]:
                                    if flow not in tainted_sinks[v]["source"][src]:
                                        tainted_sinks[v]["source"][src].append(flow)

                        tainted_sinks[v]["is_sanitized"] = tainted_vars.get_is_sanitized(v)
                    else:
                        tainted_sinks[v] =  {
                                            "source": tainted_vars.get_sources(v),
                                            "is_sanitized": tainted_vars.get_is_sanitized(v)
                                            }
        # No vars or calls were assigned, every target is no longer tainted!
        elif(clean):
            for v in target_ids:
                if(v in tainted_vars.vars):
                    tainted_vars.vars.pop(v)
                    
        # Sanity check: no vars where at least one source has no sanit flow can be unsanitized
        # but if no sanitized flows exist, it is surely unsanitized
        for var in tainted_vars.vars:
            for s in tainted_vars.get_sources(var):
                if(tainted_vars.get_sanitized_flows(var, s) == []):
                    tainted_vars.set_sanitized(var, False)
                    break

    def check_for_implicit_flows(line, tainted_vars, instantiated_vars, tainted_sinks, temporary_instantiated_vars):
        
        # Get every var used in the condition
        varsUsedInCond = getComparisonIDs(line["test"])
        callsInCond = getAssignmentCalls(line["test"])
        varsUsed = getComparisonIDs(line)
        
        temporary_instantiated_vars = instantiated_vars

        possibleSources = {}
        possiblyImplicit = False
        
        print("run implicit: ", temporary_instantiated_vars)
        
        # If a tainted var is used in the comparison, we can consider every following 
        # step that leads to a sink an implicit flow
        
        for var in varsUsedInCond:
            if(var not in instantiated_vars):
                possiblyImplicit = True
                
            elif(var in tainted_vars.vars):
                possiblyImplicit = True
                
        for call in callsInCond:
            if(getCallID(call) in entry_points):
                possiblyImplicit = True
                
        if(possiblyImplicit):
            for var in varsUsedInCond:
                # TODO problem here: ao fazer chained ifs, isto vai considerar vars que podem ter sido instantiated como uninstanciated
                # solução: Temporary list of instanciated vars
                if(var not in temporary_instantiated_vars):
                    print("-implicit flows: uninit var found",var)
                    possibleSources[var] = []
                    
                elif(var in tainted_vars.vars):
                    s = tainted_vars.get_all_sources_from_var(var)
                    sf = tainted_vars.get_all_sanitized_flows_from_var(var)
                    for source in s:
                            possibleSources[source] = sf
                    
                # Add every var in cond as a possible source if an implicit flow is possible
                elif(var not in tainted_vars.vars):
                    possibleSources[var] = []
                    
            for call in callsInCond:
                possibleSources.update(get_sources_sanitflows_from_call(call))
            
            # If we are considering implicit flows, every variable that interacts with these implicitly tainted vars 
            # must also be considered implicitly tainted
            # So we update the tainted_vars to consider every new implicitly tainted var
            # TODO: We also must consider sanitization of these variables 
            
            # get every target in the assignments and update temporary init vars
            assigns = getNodesOfType(line, "Assign")
            for a in assigns:
                target_ids = getAssignmentTargets(a)
                for t in target_ids:
                    if(t not in temporary_instantiated_vars):
                        print("- Added to instantiated vars:",t)
                        temporary_instantiated_vars.append(t)
            
            
            for var in varsUsed:
                if(var not in tainted_vars.vars):
                    tainted_vars.add_new(var, False, possibleSources)
                else:
                    for s in possibleSources:
                        tainted_vars.add_sanitized_flow(var, s, possibleSources[s])
        
        # check for body inside conditional
        if(line["ast_type"] in ["If","While"]):
            # No need to check in "orelse", as they dont exist after the multitree
            for l in getLines(line):
                if(l["ast_type"] in ["If","While"]):
                    check_for_implicit_flows(l, tainted_vars, temporary_instantiated_vars, tainted_sinks, temporary_instantiated_vars)

    def check_for_tainted_assignments(assignments, tainted_vars, instantiated_vars, tainted_sinks, clean):

        for assignment in assignments:
            calls = getAssignmentCalls(assignment)
            
            """ List of variable ids that were used on the right side of the assignment """
            var_ids = getAssignmentValues(assignment)

            """ List of target variables, used on the left side of the assignment """
            target_ids = getAssignmentTargets(assignment)

            update_instantiated_variables(instantiated_vars, target_ids)
            
            add_tainted_vars_to_dict(tainted_vars, instantiated_vars, var_ids, calls, target_ids, tainted_sinks,clean)
            
            #print("tainted vars:",tainted_vars.vars)

    def check_for_lonely_call_tainting(line, tainted_vars, tainted_sinks, instantiated_vars):
        lonely_calls = getNodesOfType(line, "Call")
        for call in lonely_calls:
            get_sources_sanitflows_from_call(call, tainted_vars, instantiated_vars, tainted_sinks)

        #tainted_sinks.extend(get_tainted_sinks(line, tainted_vars=tainted_vars, called_ids=called_ids))

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

    tainted_sinks = {}

    for line in getLines(tree):
        clean_untainted_targets = True # When in conditionals with implicit flows
                                        # Even clean assignments can pass taint
        
        # check implicit flows if conditionals exist
        if(checkImplicit):
            if(line["ast_type"] == "If" or line["ast_type"] == "While"):
                clean_untainted_targets = False
                check_for_implicit_flows(line, tainted_vars=tainted_vars, instantiated_vars=instantiated_vars, 
                                                tainted_sinks=tainted_sinks, temporary_instantiated_vars=[])
        
        # Also check for explicit flows
        assignments = getNodesOfType(line, "Assign")

        if assignments != []:
            check_for_tainted_assignments(assignments, tainted_vars=tainted_vars, instantiated_vars=instantiated_vars, 
                                        tainted_sinks=tainted_sinks, clean=(clean_untainted_targets and checkImplicit))
            
        else:
            calls = getNodesOfType(line, "Call")
            if(calls != []):
                check_for_lonely_call_tainting(line, tainted_vars=tainted_vars, tainted_sinks=tainted_sinks, instantiated_vars=instantiated_vars)
        
    return tainted_sinks
