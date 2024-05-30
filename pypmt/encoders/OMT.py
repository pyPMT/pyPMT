from copy import deepcopy
from collections import defaultdict

from z3 import *

from unified_planning.shortcuts import *

from pypmt.encoders.basic import EncoderGrounded
from pypmt.encoders.utilities import str_repr

from pypmt.modifiers.modifierLinear import LinearModifier
from pypmt.modifiers.modifierParallel import ParallelModifier

import networkx as nx
import itertools

class EncoderOMT(EncoderGrounded):

    """
    Add references 
    """
    def __init__(self, name, task, modifier):
        super().__init__(name, task, modifier)
        self.allow_multiple_actions_per_step=False

        # Auxiliary variables
        # this is a mapping from the UP ground actions to z3 and back
        self.aux_z3_actions_to_up = dict() # multiple z3 vars point to one grounded fluent
        self.up_actions_to_aux_z3 = defaultdict(list)
        
        # mapping from up fluent to Z3 var
        self.up_fluent_to_aux_z3 = defaultdict(list) 

    def create_aux_variables(self, t):
        """! 
        Create the Z3 auxiliary variables for step t.
        @param t: the step we want to encode
        @returns: None
        """

        # for actions
        for grounded_action in self.ground_problem.actions:
            key   = str_repr(grounded_action)
            keyt  = "abs_" + key
            act_var = z3.Bool(keyt, ctx=self.ctx)
            self.up_actions_to_aux_z3[key].append(act_var)
            self.aux_z3_actions_to_up[act_var] = key

        # for fluents
        grounded_up_fluents = [f for f, _ in self.ground_problem.initial_values.items()]
        for grounded_fluent in grounded_up_fluents:
            key  = str_repr(grounded_fluent)
            keyt = "mod_" + key
            if grounded_fluent.type.is_real_type() or grounded_fluent.type.is_bool_type():
                self.up_fluent_to_aux_z3[key].append(z3.Bool(keyt, ctx=self.ctx))
            else:
                raise TypeError

        

    def encode(self,t):

        # If we encode the first step, we return the "abstract" formula,
        # as this has already been encoded
        if t == 0:
            self.base_encode()
            return deepcopy(self.formula)

        # Otherwise we do the proper substitutions
        self.create_variables(t+1)  # base_encode added vars for step 0, so we only need to add t+1
        
        
        list_substitutions = [] # list of pairs (from,to)
        for key in self.up_actions_to_z3.keys():
            list_substitutions.append(
                (self.up_actions_to_z3[key][0],
                 self.up_actions_to_z3[key][t]))
        for key in self.up_fluent_to_z3.keys():
            list_substitutions.append(
                (self.up_fluent_to_z3[key][0],
                 self.up_fluent_to_z3[key][t]))
            list_substitutions.append(
                (self.up_fluent_to_z3[key][1],
                 self.up_fluent_to_z3[key][t + 1]))
    
        # Start encoding basic building block using rename variables from substitution  
        encoded_formula = dict()
        encoded_formula['initial']    = self.formula['initial']
        encoded_formula['actions']    = substitute(self.formula['actions'], list_substitutions)
        encoded_formula['goal']    = z3.substitute(self.formula['goal'], list_substitutions)

        encoded_formula['frame'] = substitute(self.formula['frame'], list_substitutions)
        encoded_formula['sem'] = substitute(self.formula['sem'], list_substitutions)

        encoded_formula['abstract_actions']    = substitute(self.formula['abstract_actions'], list_substitutions)
        encoded_formula['abstract_goal']       = substitute(self.formula['abstract_goal'], list_substitutions)
        encoded_formula['loop_formulas']       = substitute(self.formula['loop_formulas'], list_substitutions)

        # TODO: this will probably have be adapted, depending on whether a metric is provided in the PDDL or not.
        encoded_formula['objective']       = self.formula['objective']


        return encoded_formula

    def base_encode(self):
        """!
        Builds based OMT encoding.
        Populates the formula dictionary, where all the "raw" formulas are stored
        @return None
        """
        self.create_variables(0) # Create variables for the initial state
        self.create_variables(1)
        self.create_aux_variables(1) 
        self._populate_modifiers() # do indices

        self.formula['initial'] = z3.And(self.encode_initial_state())  # Encode initial state axioms
        self.formula['actions'] = z3.And(self.encode_actions(0))  # Encode universal axioms
        self.formula['frame']   = z3.And(self.encode_frame(0))  # Encode explanatory frame axioms
        self.formula['sem']     = z3.And(self.encode_execution_semantics())  # Encode execution semantics (lin/par)    
        self.formula['goal']    = z3.And(self.encode_goal_state(0))  # Encode goal state axioms

        # Abstract encoding
        self.formula['abstract_actions'] = z3.And(self.encode_abstract_actions(0)) # Encode relaxed universal axioms
        self.formula['abstract_goal']    = z3.And(self.encode_abstract_goal_state(0))  # Encode abstract goal state axioms
        self.formula['loop_formulas']    = z3.And(self.encode_loop_formulas(0)) # Encode loop formula

        # Objective
        self.formula['objective'] = self.encode_objective()
       
     
    def _free_to_abs_variables(self,formula,t):
        fluents = formula.environment.free_vars_extractor.get(formula)
                
        vars = []
        for f in fluents:
            key = str_repr(f)
            var = self.up_fluent_to_aux_z3[key][t]
            vars.append(var)
        return vars
    
    def encode_abstract_actions(self, t):
        """!
        Encodes the abstract Actions
        @return actions: list of Z3 formulas asserting the abstract actions

        """
        abstract_actions = []

        # For each fluent, store actions that assign that fluent in their effects
        look_up_table = defaultdict(list, { k[t]:[] for k in self.up_fluent_to_aux_z3.values() })

        for grounded_action in self.ground_problem.actions:
            key = str_repr(grounded_action)
            action_var = self.up_actions_to_aux_z3[key][-1] # need the last one

            # create the action abstract precondition
            action_pre = []
            for pre in grounded_action.preconditions:
                vars = self._free_to_abs_variables(pre,-1)                
                action_pre.append(z3.Or(self._expr_to_z3(pre, t+1),z3.Or(vars)))
        
            
            # create the action abstract effect on auxiliary variables
            action_eff = []
            for eff in grounded_action.effects:
                key = str_repr(eff.fluent)
                var = self.up_fluent_to_aux_z3[key][-1]
                
                action_eff.append(var)

                look_up_table[var].append(action_var)
            
            
            # assert universal
            abstract_actions.append(z3.Implies(action_var, z3.And(action_pre)))
            abstract_actions.append(z3.Implies(action_var, z3.And(action_eff)))
            
        # Ensure that auxiliary variables are true only if corresponding abstract action is executed
        for key,val in look_up_table.items():
            if len(val) > 0:
                abstract_actions.append(z3.Implies(key, z3.Or(val)))
            else:
                abstract_actions.append(z3.Implies(key, False))

        return abstract_actions

    def encode_abstract_goal_state(self, t):
            """!
            Encodes formula defining abstract goal state
            @return goal: Z3 formula asserting propositional and numeric subgoals
            """
            # TODO: assuming conjunctive goals for now
            goal = []
            for goal_pred in self.task.goals:
                vars = self._free_to_abs_variables(goal_pred,-1)
                goal.append(z3.Or(self._expr_to_z3(goal_pred, t+1), z3.Or(vars)))
            return goal
    
    def encode_loop_formulas(self,t):
        """!
            Encodes loop formulas to forbid self-enabling abstract actions
            @return goal: Z3 formula asserting loop formulas
        """
        loop_formula = []

        dgraph_edges = self._build_d_graph_edges()

        loops = self._identify_scc(dgraph_edges)
        
        for loop in loops:
            l_vars = []
            r_vars = []


            for grounded_action in self.ground_problem.actions:
                    effects = set([eff.fluent for eff in grounded_action.effects])

                    if len(loop & effects) > 0:
                        
                        action_pre = []
                        for pre in grounded_action.preconditions:
                            flat_abstract_pre = self._free_to_abs_variables(pre,-1)    
                            flat_abstract_pre.append(self._expr_to_z3(pre, t+1))            
                            action_pre.append(flat_abstract_pre)
                        
                        
                        for l in list(loop):
                            key = str_repr(l)
                            var = self.up_fluent_to_aux_z3[key][-1]
                            if var not in l_vars:
                                l_vars.append(var)


                        if len(action_pre) == 1:
                            for cond in action_pre[0]:
                                if cond in l_vars:
                                    pass
                                else:
                                    r_vars.append(cond)

                        else:

                            dnf = list(itertools.product(*action_pre))
                            
                            for combo in dnf:
                                if len(set(l_vars) & set(combo)) > 0:
                                    pass
                                else:
                                    r_vars.append(z3.And(combo))


            loop_formula.append(z3.Implies(z3.Or(l_vars),z3.Or(r_vars)))
            
        return loop_formula
    
    def _build_d_graph_edges(self):

        edges = []

        # nodes in the dependency graph are either concrete preconditions (step #1) or
        # auxiliary variables corresponding to fluents appearing in the concrete preconditions (step #2)
        # For convenience step #2 below operates on fluents as opposed to auxiliary variables. 
        # The reasoning is still the same but it facilitates later steps - the fluent will be converted to
        # an auxiliary variable later when encoding the loop formula.

        for grounded_action in self.ground_problem.actions:
                     
            for eff in grounded_action.effects:

                for pre in grounded_action.preconditions:
                    edges.append((eff.fluent,pre))
            
                    for fluent in pre.environment.free_vars_extractor.get(pre):
                        edges.append((eff.fluent,fluent)) 
                    
                    

        return set(edges)
    
    def _identify_scc(self, edges):

        graph = nx.DiGraph()
        graph.add_edges_from(edges)

        self_loops = set(nx.nodes_with_selfloops(graph))

        scc = []
        for el in nx.strongly_connected_components(graph):
            if len(el) > 1:
                scc.append(el)
            elif len(el & self_loops):
                scc.append(el)
            else:
                continue # discard  indiviual nodes with no self-loops
        
        return scc 
                     
    def encode_objective(self):

        objective = []

        if len(self.ground_problem.quality_metrics) > 0:
            print(self.ground_problem.quality_metrics)
            raise
        else:
            
            for grounded_action in self.ground_problem.actions:
                key = str_repr(grounded_action)
                abs_action_var = self.up_actions_to_aux_z3[key][-1]
                objective.append(z3.If(abs_action_var,1.0,0.0))

                for a in self.up_actions_to_z3[key]:
                    objective.append(z3.If(a,1.0,0.0))
        
        return sum(objective)

   


class EncoderSequentialOMT(EncoderOMT):
    """
    Class that encodes a problem to a classical sequential encoding to SMT
    """
    def __init__(self, task):
        super().__init__("omtseq", task, LinearModifier())
        self.allow_multiple_actions_per_step = False

class EncoderParallelOMT(EncoderOMT):
    """
    Class that encodes a problem to a parallel encoding to SMT using the forall-step semantics
    TODO: Check this is really forall-step semantics
    """
    def __init__(self, task):
        raise NotImplementedError("Can't use parallel encoding for now.") #TODO: need mutexes for this

        super().__init__(task, ParallelModifier())
        self.allow_multiple_actions_per_step = True
        self.name = "omt-seqForall"  # set the planner name.



    def encodeASAP(self,t):

        actions = []
        for grounded_action in self.ground_problem.actions:
            key = str_repr(grounded_action)
            # Fetch variable for action at current step t
            action_current = self.up_actions_to_z3[key][t]

            # Fetch variable for action at previous step t-1
            action_previous = self.up_actions_to_z3[key][t-1]

            # Fetch action preconditions
            action_pre = []
            for pre in grounded_action.preconditions:
                action_pre.append(self._expr_to_z3(pre, t))






# from z3 import *
# from collections import defaultdict
# from copy import deepcopy
# from timeit import default_timer as timer
# import itertools

# from unified_planning.shortcuts import *
# from unified_planning.engines import CompilationKind
# from unified_planning.model.operators import *
# from unified_planning.model.walkers import *

# import networkx as nx

# from .base import Encoder

# from omtplan.modifiers.modifierLinear import LinearModifier
# from omtplan.modifiers.modifierParallel import ParallelModifier

# from omtplan.encoders.utilities import str_repr

# def buildDTables(encoder):
#     """!
#     Extracts information needed to build dependency graph.

#     @param encoder
#     @return edges: edges of the dependency graph.
#     @return table: datastructure containing info to build loop formula.
#     """
    
#     # Edges of dependency graph
#     edges = []

#     # Also builds lookup table
#     # to store pre/eff for each action
#     # needed to build loop formula

#     table = defaultdict(dict)

#     step = encoder.horizon + 1
#     for action in encoder.ground_problem.actions:
#         # preconditions of action
#         tpre = []

#         # relaxed preconditions of action
#         tpre_rel = []

#         # effects of action
#         teff = []

#         # Append preconditions
#         for pre in action.preconditions:
#             if pre.node_type in [OperatorKind.FLUENT_EXP, OperatorKind.NOT]:
#                 for var_name in FreeVarsExtractor().get(pre):
#                     tpre.append(encoder.touched_variables[str(var_name)])
#                     if pre.node_type == OperatorKind.NOT:
#                         tmp = [z3.Not(encoder.boolean_variables[step-1][str(var_name)]), encoder.touched_variables[str(var_name)]]
#                     else:
#                         tmp = [encoder.boolean_variables[step-1][str(var_name)],encoder.touched_variables[str(var_name)]]
                    
#                     tpre_rel.append(tuple(tmp))
#             else:
#                 expr = inorderTraverse(pre, encoder.problem_z3_variables, step-1, encoder.problem_constant_numerics)
#                 tmp = [expr]
#                 for var_name in FreeVarsExtractor().get(pre):
#                     tpre.append(encoder.touched_variables[str(var_name)])
#                     tmp.append(encoder.touched_variables[str(var_name)])
#                 tpre_rel.append(tuple(tmp))
            
#         # TODO: These is a bug here, the but is that the edges should be between two predicates, not between mulitple predicates.

                            
#         # Append effects.
#         for effect in action.effects:
#             if str(effect.fluent) in encoder.touched_variables and not str(effect.fluent) in encoder.var_objective:
#                 teff.append(encoder.touched_variables[str(effect.fluent)])
        
#         ## Pupulate edges
#         for p in tpre:
#             for e in teff:
#                 edges.append((e,p))

#         ## Fill lookup table

#         table[action.name]['pre']     = tpre
#         table[action.name]['pre_rel'] = tpre_rel
#         table[action.name]['eff']     = teff
        
#         if len(action.conditional_effects) > 0:
#             raise Exception("Conditional effects are not supported yet")

#     ## Remove duplicate edges
#     edges = set(edges)

#     return edges, table

# def computeSCC(edges):
#     """!
#     Computes Strongly Connected Components of graph.

#     @param edges: edges of graph
#     @return scc_purged: list of scc
#     """

#     g = nx.DiGraph()

#     g.add_edges_from(edges)

#     scc_original = nx.strongly_connected_components(g)

#     self_loops = set([n for n in nx.nodes_with_selfloops(g)])

#     scc_purged = []

#     for scc in scc_original:

#         if len(scc) == 1:
#             if len(scc & self_loops) > 0:
#                 scc_purged.append(scc)
#         else:
#             scc_purged.append(scc)

#     return scc_purged

# def encodeLoopFormulas(encoder):
#     """!
#     Builds loop formulas (see paper for description).

#     @param encoder
#     @return lf: list of loop formulas.
#     """
    
#     lf = []

#     ## reverse map touched vars
#     inv_touched_variables = {v: k for k, v in encoder.touched_variables.items()}

#     ## compute data to build loop formulas
#     edges, table = buildDTables(encoder)

#     # Loop formula for loop L: V L => V R(L)

#     ## Compute SCC (i.e., loops)
#     scc = computeSCC(edges)

#     for loop in scc:

#         L = []
#         R = []

#         # for each var in loop we check what actions can be added
#         for variable in list(loop):

#             # first build set L containing loop atoms
#             z3_var = inv_touched_variables.get(variable,None)
#             if z3_var is not None:
#                 L.append(encoder.touched_variables[z3_var])
#             else:
#                 raise Exception("Could not find key to build loop formula")

#         # for each action check if conditions to build R are met
#         for action in table.keys():
#             # variables appears in effect of action at step n
#             if len(set(table[action]['eff']) & loop) > 0:
#                 # now check if variables appears in pre of action at step n+1
#                 # if list of precondition has length one: we just a simple condition
#                 # e.g. x v tx -> tuple(x,tx)
#                 # no need to check dnf
#                 # otherwise check all disjunct of dnf
#                 if len(table[action]['pre_rel']) == 1:
#                     for cond in table[action]['pre_rel'][0]:
#                         if cond in loop:
#                             pass
#                         else:
#                             R.append(cond)
#                 else:
#                     # if precondition has several terms, e.g. tx & (ty v tz),
#                     # need to check for all possible combinations, i.e., tx & ty v tx & tz

#                     dnf = list(itertools.product(*table[action]['pre_rel']))

#                     for combo in dnf:
#                         if len(set(combo) & loop) > 0:
#                             pass
#                         else:
#                             R.append(z3.And(combo))
#         lf.append(z3.Implies(z3.Or(L), z3.Or(set(R))))
#     return lf


# class EncoderOMT(Encoder):
#     """
#     Class that defines method to build SMT encoding.
#     """
#     def __init__(self, task, modifier):
#         Encoder.__init__(self, task, modifier, False)

#         self.name = "omt"  # set the planner name.
#         self.formula = defaultdict(list)  # Store the "raw" formula that we will later instantiate
#         self.base_encode()  # Now create the raw formulas

#     def base_encode(self):
#         self.createVariables(0)  # Create variables for the initial state
#         self.createVariables(1)  # Create variables for the initial state

#     def encodeObjective(self):
#         """!
#         Encodes objective function. If domain is metric it builds a Z3 formula
#         encoding the metric, otherwise it builds a pseudo Boolean objective
#         (i.e., we pay one each time an action is executed).

#         @return objective: objective function.
#         """

#         objective = []
#         if len(self.ground_problem.quality_metrics) > 0:
#             for metric in deepcopy(self.ground_problem.quality_metrics):
#                 objective.append(inorderTraverse(metric.expression, self.problem_z3_variables, self.horizon, self.problem_constant_numerics) )
#         else:
#             objective = []
#             for step in range(self.horizon):
#                 for action in self.action_variables[step].values():
#                     objective.append(z3.If(action,1.0,0.0))
#         objective = sum(objective) if len(objective) > 0 else objective
#         return objective

#     def createAuxVariables(self):
#         """
#         Creates auxiliary variables used in relaxed suffix (see related paper).

#         """

#         # create relaxed state variables: x -> tx
#         self.touched_variables = dict()

#         step = self.horizon + 1

#         for var_name in self.boolean_variables[0].keys():
#             self.touched_variables[var_name] = z3.Bool('t{}_{}'.format(var_name,self.horizon+1))

#         for var_name in self.numeric_variables[0].keys():
#             self.touched_variables[var_name] = z3.Bool('t{}_{}'.format(var_name,self.horizon+1))

#         # create sets of relaxed action variables for
#         # steps n, n+1

#         self.auxiliary_actions = defaultdict(dict)

#         for step in range(self.horizon,self.horizon+2):
#             for action in self.ground_problem.actions:
#                 self.auxiliary_actions[step][action.name] = z3.Bool('{}_{}'.format(action.name,step))

#     def encodeRelaxedGoal(self):
#         """!
#         Encodes relaxed goals.

#         @return goal: relaxed goal formula
#         """
#         return inorderTraverse(self.ground_problem.goals, self.problem_z3_variables, self.horizon, self.problem_constant_numerics, self.touched_variables)

#     def encodeAdditionalCosts(self):
#         """!
#         Encodes costs for relaxed actions that may be executed in the suffix.
#         At each step, we define a cost variables that is equal to the summation of
#         pseudoboolean terms (if action is executed we pay a price -- see paper)

#         @return sum of additional costs
#         @return cost contraints
#         """

#         costs = []
#         constraints = []

#         for step in range(self.horizon,self.horizon+2):
#             cost = z3.Real('add_cost_{}'.format(step))
#             total = []
#             for a,v in self.auxiliary_actions[step].items():
#                 if len(self.ground_problem.quality_metrics) > 0:
#                     total.append(z3.If(v,1.0*sum(self.final_costs[a]),0.0))
#                 else:
#                     total.append(z3.If(v,1.0,0.0))
#             constraints.append(cost == sum(total))
#             costs.append(cost)

#         constraints = z3.And(constraints)

#         return sum(costs), constraints

#     def encodeOnlyIfNeeded(self):
#         """!
#         Enforces that auxiliary variables can be executed only ifall steps before
#         the suffix are filled with at least one action.

#         @return list of Z3 constraints.
#         """

#         c = []

#         for step in range(self.horizon,self.horizon+2):
#             rel_a = list(self.auxiliary_actions[step].values())
#             actions = []
#             for index in range(self.horizon):
#                 actions.append(z3.Or(list(self.action_variables[index].values())))
#             c.append(z3.Implies(z3.Or(rel_a), z3.And(actions)))

#         return c

#     def encodeRelaxedActions(self):
#         """!
#         Encodes relaxed universal axioms.

#         @return relax: list of Z3 formulas
#         """

#         # dictionary used to store variables corresponding to concrete costs
#         # at last step n
#         self.final_costs = defaultdict(list)

#         # list of relaxed universal axioms
#         relax = []
#         step = self.horizon

#         for action in self.ground_problem.actions:
#             # Append preconditions
#             for pre in action.preconditions:
#                 precondition = inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
#                 relax.append(z3.Implies(self.auxiliary_actions[step][action.name], precondition))

#             # Append effects.
#             for effect in action.effects:
#                 if str(effect.fluent) in self.touched_variables:
#                     relax.append(z3.Implies(self.auxiliary_actions[step][action.name], self.touched_variables[str(effect.fluent)]))

#         return relax

#     def encodeASAP(self):
#         """!
#         Encodes constraints that push execution of actions as early as possible.

#         @return list of Z3 formulas.
#         """
#         # ASAP constraint are enforced both for concrete and relaxed actions
#         all_actions  = self.action_variables.copy()
#         all_actions.update(self.auxiliary_actions)

#         c = []

#         for step in range(self.horizon+1):
#             for action in self.ground_problem.actions:
#                 # Condition 1: action already executed at
#                 # previous step
#                 act_pre = all_actions[step][action.name]

#                 # Condition 2: one of the prec of action was violated
#                 violated = []

#                 # Append preconditions
#                 for pre in action.preconditions:
#                     precondition = inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
#                     violated.append(z3.Not(precondition))

#                 # Condition 3: a mutex was executed a previous step
#                 # return all actions that are in mutex with the
#                 # current action
#                 mutex = [(lambda t:  t[1] if t[0] == action else t[0])(t) for t in self.modifier.mutexes if action in t]
#                 # fetch action variable
#                 mutex_vars = [all_actions[step][a.name] for a in mutex]

#                 # ASAP constraint
#                 act_post = all_actions[step+1][action.name]
#                 c.append(z3.Implies(act_post, z3.Or(act_pre, z3.Or(violated), z3.Or(mutex_vars))))

#         return c

#     def encodeTransitiveClosure(self):
#         """!
#         Encodes computation of transitive closure at step n+1  (see related paper).

#         @return trac: Z3 formulas that encode computation of transitive closure.
#         """
#         trac = []
#         step = self.horizon+1

#         for action in self.ground_problem.actions:
#             # Append preconditions
#             for pre in action.preconditions:
#                 touched_vars = []
#                 for var in FreeVarsExtractor().get(pre):
#                     if str(var) in self.touched_variables:
#                         touched_vars.append(self.touched_variables[str(var)])
#                 precondition = inorderTraverse(pre, self.problem_z3_variables, step-1, self.problem_constant_numerics)
#                 trac.append(z3.Implies(self.auxiliary_actions[step][action.name], z3.Or(precondition, z3.Or(touched_vars))))

#             # Append effects.
#             for effect in action.effects:
#                 if str(effect.fluent) in self.touched_variables:
#                     trac.append(z3.Implies(self.auxiliary_actions[step][action.name], self.touched_variables[str(effect.fluent)]))

#         sentinel = object()
#         # Encode frame axioms for boolean fluents
#         for fluent in self.all_problem_fluents:
#             if fluent.type.is_bool_type():
#                 # Encode frame axioms only if atoms have SMT variables associated
#                 action_eff = []
#                 for action in self.ground_problem.actions:
#                     effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]

#                     for ele in effects_fluents:
#                         if str(ele.fluent) == str(fluent):
#                             if ele.value.is_true():
#                                 action_eff.append(self.auxiliary_actions[step][action.name])
#                                 action_eff.append(self.auxiliary_actions[step-1][action.name])
#                             else:
#                                 action_eff.append(self.auxiliary_actions[step][action.name])
#                                 action_eff.append(self.auxiliary_actions[step-1][action.name])
#                 trac.append(z3.Implies(self.touched_variables[str(fluent)], z3.Or(action_eff)))

#             elif fluent.type.is_int_type() or fluent.type.is_real_type():
#                 action_num = []
#                 for action in self.ground_problem.actions:
#                     effects_fluents = [effect for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()]
#                     for ele in effects_fluents:
#                         if str(ele.fluent) == str(fluent):
#                             action_num.append(self.auxiliary_actions[step][action.name])
#                             action_num.append(self.auxiliary_actions[step-1][action.name])
#                 trac.append(z3.Implies(self.touched_variables[str(fluent)], z3.Or(action_num)))
#             else:
#                 raise Exception("Unknown fluent type {}".format(fluent.type))

#         return trac

#     def _expr_to_z3(self, expr, t, c=None):
#             """
#             Traverses a tree expression in-order and converts it to a Z3 expression.
#             expr: The tree expression node. (Can be a value, variable name, or operator)
#             t: The timestep for the Fluents to be considered 
#             c: A context manager, as we need to take into account parameters from actions, fluents, etc ...
#             Returns A Z3 expression or Z3 value.
#             """
#             if isinstance(expr, int): # A python Integer
#                 return z3.IntVal(expr, ctx=self.ctx)
#             elif isinstance(expr, bool): # A python Boolean
#                 return z3.BoolVal(expr, ctx=self.ctx)

#             elif isinstance(expr, Effect): # A UP Effect
#                 eff = None
#                 if expr.kind == EffectKind.ASSIGN:
#                     eff = self._expr_to_z3(expr.fluent, t + 1, c) == self._expr_to_z3(expr.value, t, c)
#                 if expr.kind == EffectKind.DECREASE:
#                     eff = self._expr_to_z3(expr.fluent, t + 1, c) == self._expr_to_z3(expr.fluent, t, c) - self._expr_to_z3(expr.value, t, c)
#                 if expr.kind == EffectKind.INCREASE:
#                     eff = self._expr_to_z3(expr.fluent, t + 1, c) == self._expr_to_z3(expr.fluent, t, c) + self._expr_to_z3(expr.value, t, c)
#                 if expr.is_conditional():
#                     return z3.Implies(self._expr_to_z3(expr.condition, t, c) , eff)
#                 else:
#                     return eff

#             elif isinstance(expr, FNode): # A UP FNode ( can be anything really )
#                 if expr.is_object_exp(): # A UP object
#                     raise ValueError(f"{expr} should not be evaluated")
#                 elif expr.is_constant(): # A UP constant
#                     return expr.constant_value()
#                 elif expr.is_or():  # A UP or
#                     return z3.Or([self._expr_to_z3(x, t, c) for x in expr.args])
#                 elif expr.is_and():  # A UP and
#                     return z3.And([self._expr_to_z3(x, t, c) for x in expr.args])
#                 elif expr.is_fluent_exp(): # A UP fluent
#                     return self.up_fluent_to_z3[str_repr(expr)][t]
#                 elif expr.is_parameter_exp():
#                     raise ValueError(f"{expr} should not be evaluated")
#                 elif expr.is_lt():
#                     return self._expr_to_z3(expr.args[0], t, c) < self._expr_to_z3(expr.args[1], t, c)
#                 elif expr.is_le():
#                     return self._expr_to_z3(expr.args[0], t, c) <= self._expr_to_z3(expr.args[1], t, c)
#                 elif expr.is_times():
#                     return self._expr_to_z3(expr.args[0], t, c) * self._expr_to_z3(expr.args[1], t, c)
#                 elif expr.is_plus():
#                     return z3.Sum([self._expr_to_z3(x, t, c) for x in expr.args])
#                 elif expr.is_minus():
#                     return self._expr_to_z3(expr.args[0], t, c) - self._expr_to_z3(expr.args[1], t, c)
#                 else:
#                     raise TypeError(f"Unsupported expression: {expr} of type {type(expr)}")
#             else:
#                 raise TypeError(f"Unsupported expression: {expr} of type {type(expr)}")

#     def encode(self,horizon):
#         """!
#         Builds OMT encoding.

#         @param horizon: horizon for bounded planning formula.
#         @return formula: dictionary containing subformulas.
#         """

#         self.horizon = horizon

#         # set the planner name.
#         self.name = "omt"

#         # Create variables
#         self.createVariables(horizon+1)

#         # Start encoding formula
#         formula = defaultdict(list)

#         # Encode initial state axioms
#         formula['initial'] = self.encodeInitialState()

#         # Encode universal axioms
#         formula['actions'] = self.encodeActions()

#         # Encode explanatory frame axioms
#         formula['frame'] = self.encodeFrame()

#         # Encode execution semantics (lin/par)
#         formula['sem'] = self.encodeExecutionSemantics()

#         #
#         # Encode relaxed suffix
#         #

#         # Remove this for now.
#         self.var_objective = parseMetric(self)

#         # Create auxiliary variables
#         self.createAuxVariables()

#         # Encode objective function
#         formula['objective'] = self.encodeObjective()

#         # Encode relaxed transition T^R
#         formula['tr'] = self.encodeRelaxedActions()

#         # Encode transitive closure
#         formula['tc'] = self.encodeTransitiveClosure()

#         # Encode ASAP constraints
#         formula['asap'] = self.encodeASAP()

#         # Encode relaxed  goal state axioms
#         goal = self.encodeGoalState()
#         formula['real_goal'] = z3.And(goal)
#         abstract_goal = self.encodeRelaxedGoal()
#         formula['goal'] = z3.Or(z3.And(goal),abstract_goal)

#         # Encode loop formula
#         formula['lf'] = encodeLoopFormulas(self) # This needs to be fixed.

#         # Encode additional cost for relaxed actions
#         add_objective, add_constraints = self.encodeAdditionalCosts()
#         formula['objective'] = formula['objective'] + add_objective
#         formula['additional_constraints'] = add_constraints

#         # Perform relaxed actions only if previous steps are filled
#         formula['oin'] = self.encodeOnlyIfNeeded()

#         return formula

# class EncoderSequentialOMT(EncoderOMT):
#     """
#     Class that encodes a problem to a classical sequential encoding to SMT
#     """
#     def __init__(self, task):
#         super().__init__(task, LinearModifier())
#         self.name = "SequentialOMT"  # set the planner name.

# class EncoderParallelOMT(EncoderOMT):
#     """
#     Class that encodes a problem to a parallel encoding to SMT using the forall-step semantics
#     TODO: Check this is really forall-step semantics
#     """
#     def __init__(self, task):
#         super().__init__(task, ParallelModifier(True))
#         self.name = "ForallOMT"  # set the planner name.

    