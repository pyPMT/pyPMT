from z3 import *
from collections import defaultdict
from copy import deepcopy
from timeit import default_timer as timer
import itertools

from unified_planning.shortcuts import *
from unified_planning.engines import CompilationKind
from unified_planning.model.operators import *
from unified_planning.model.walkers import *

import networkx as nx

from .base import Encoder

from pypmt.modifiers.modifierLinear import LinearModifier
from pypmt.modifiers.modifierParallel import ParallelModifier

from pypmt.encoders.utilities import str_repr

def buildDTables(encoder):
    """!
    Extracts information needed to build dependency graph.

    @param encoder
    @return edges: edges of the dependency graph.
    @return table: datastructure containing info to build loop formula.
    """
    
    # Edges of dependency graph
    edges = []

    # Also builds lookup table
    # to store pre/eff for each action
    # needed to build loop formula

    table = defaultdict(dict)

    step = encoder.horizon + 1
    for action in encoder.ground_problem.actions:
        # preconditions of action
        tpre = []

        # relaxed preconditions of action
        tpre_rel = []

        # effects of action
        teff = []

        # Append preconditions
        for pre in action.preconditions:
            if pre.node_type in [OperatorKind.FLUENT_EXP, OperatorKind.NOT]:
                for var_name in FreeVarsExtractor().get(pre):
                    tpre.append(encoder.touched_variables[str(var_name)])
                    if pre.node_type == OperatorKind.NOT:
                        tmp = [z3.Not(encoder.boolean_variables[step-1][str(var_name)]), encoder.touched_variables[str(var_name)]]
                    else:
                        tmp = [encoder.boolean_variables[step-1][str(var_name)],encoder.touched_variables[str(var_name)]]
                    
                    tpre_rel.append(tuple(tmp))
            else:
                expr = inorderTraverse(pre, encoder.problem_z3_variables, step-1, encoder.problem_constant_numerics)
                tmp = [expr]
                for var_name in FreeVarsExtractor().get(pre):
                    tpre.append(encoder.touched_variables[str(var_name)])
                    tmp.append(encoder.touched_variables[str(var_name)])
                tpre_rel.append(tuple(tmp))
            
        # TODO: These is a bug here, the but is that the edges should be between two predicates, not between mulitple predicates.

                            
        # Append effects.
        for effect in action.effects:
            if str(effect.fluent) in encoder.touched_variables and not str(effect.fluent) in encoder.var_objective:
                teff.append(encoder.touched_variables[str(effect.fluent)])
        
        ## Pupulate edges
        for p in tpre:
            for e in teff:
                edges.append((e,p))

        ## Fill lookup table

        table[action.name]['pre']     = tpre
        table[action.name]['pre_rel'] = tpre_rel
        table[action.name]['eff']     = teff
        
        if len(action.conditional_effects) > 0:
            raise Exception("Conditional effects are not supported yet")

    ## Remove duplicate edges
    edges = set(edges)

    return edges, table

def computeSCC(edges):
    """!
    Computes Strongly Connected Components of graph.

    @param edges: edges of graph
    @return scc_purged: list of scc
    """

    g = nx.DiGraph()

    g.add_edges_from(edges)

    scc_original = nx.strongly_connected_components(g)

    self_loops = set([n for n in nx.nodes_with_selfloops(g)])

    scc_purged = []

    for scc in scc_original:

        if len(scc) == 1:
            if len(scc & self_loops) > 0:
                scc_purged.append(scc)
        else:
            scc_purged.append(scc)

    return scc_purged

def encodeLoopFormulas(encoder):
    """!
    Builds loop formulas (see paper for description).

    @param encoder
    @return lf: list of loop formulas.
    """
    
    lf = []

    ## reverse map touched vars
    inv_touched_variables = {v: k for k, v in encoder.touched_variables.items()}

    ## compute data to build loop formulas
    edges, table = buildDTables(encoder)

    # Loop formula for loop L: V L => V R(L)

    ## Compute SCC (i.e., loops)
    scc = computeSCC(edges)

    for loop in scc:

        L = []
        R = []

        # for each var in loop we check what actions can be added
        for variable in list(loop):

            # first build set L containing loop atoms
            z3_var = inv_touched_variables.get(variable,None)
            if z3_var is not None:
                L.append(encoder.touched_variables[z3_var])
            else:
                raise Exception("Could not find key to build loop formula")

        # for each action check if conditions to build R are met
        for action in table.keys():
            # variables appears in effect of action at step n
            if len(set(table[action]['eff']) & loop) > 0:
                # now check if variables appears in pre of action at step n+1
                # if list of precondition has length one: we just a simple condition
                # e.g. x v tx -> tuple(x,tx)
                # no need to check dnf
                # otherwise check all disjunct of dnf
                if len(table[action]['pre_rel']) == 1:
                    for cond in table[action]['pre_rel'][0]:
                        if cond in loop:
                            pass
                        else:
                            R.append(cond)
                else:
                    # if precondition has several terms, e.g. tx & (ty v tz),
                    # need to check for all possible combinations, i.e., tx & ty v tx & tz

                    dnf = list(itertools.product(*table[action]['pre_rel']))

                    for combo in dnf:
                        if len(set(combo) & loop) > 0:
                            pass
                        else:
                            R.append(z3.And(combo))
        lf.append(z3.Implies(z3.Or(L), z3.Or(set(R))))
    return lf


class EncoderOMT(Encoder):
    """
    Class that defines method to build SMT encoding.
    """
    def __init__(self, task, modifier):
        Encoder.__init__(self, task, modifier, False)

        self.name = "omt"  # set the planner name.
        self.formula = defaultdict(list)  # Store the "raw" formula that we will later instantiate
        self.base_encode()  # Now create the raw formulas

    def base_encode(self):
        self.create_variables(0)  # Create variables for the initial state
        self.create_variables(1)  # Create variables for the initial state

    def encodeObjective(self):
        """!
        Encodes objective function. If domain is metric it builds a Z3 formula
        encoding the metric, otherwise it builds a pseudo Boolean objective
        (i.e., we pay one each time an action is executed).

        @return objective: objective function.
        """

        objective = []
        if len(self.ground_problem.quality_metrics) > 0:
            for metric in deepcopy(self.ground_problem.quality_metrics):
                objective.append(inorderTraverse(metric.expression, self.problem_z3_variables, self.horizon, self.problem_constant_numerics) )
        else:
            objective = []
            for step in range(self.horizon):
                for action in self.action_variables[step].values():
                    objective.append(z3.If(action,1.0,0.0))
        objective = sum(objective) if len(objective) > 0 else objective
        return objective

    def createAuxVariables(self):
        """
        Creates auxiliary variables used in relaxed suffix (see related paper).

        """

        # create relaxed state variables: x -> tx
        self.touched_variables = dict()

        step = self.horizon + 1

        for var_name in self.boolean_variables[0].keys():
            self.touched_variables[var_name] = z3.Bool('t{}_{}'.format(var_name,self.horizon+1))

        for var_name in self.numeric_variables[0].keys():
            self.touched_variables[var_name] = z3.Bool('t{}_{}'.format(var_name,self.horizon+1))

        # create sets of relaxed action variables for
        # steps n, n+1

        self.auxiliary_actions = defaultdict(dict)

        for step in range(self.horizon,self.horizon+2):
            for action in self.ground_problem.actions:
                self.auxiliary_actions[step][action.name] = z3.Bool('{}_{}'.format(action.name,step))

    def encodeRelaxedGoal(self):
        """!
        Encodes relaxed goals.

        @return goal: relaxed goal formula
        """
        return inorderTraverse(self.ground_problem.goals, self.problem_z3_variables, self.horizon, self.problem_constant_numerics, self.touched_variables)

    def encodeAdditionalCosts(self):
        """!
        Encodes costs for relaxed actions that may be executed in the suffix.
        At each step, we define a cost variables that is equal to the summation of
        pseudoboolean terms (if action is executed we pay a price -- see paper)

        @return sum of additional costs
        @return cost contraints
        """

        costs = []
        constraints = []

        for step in range(self.horizon,self.horizon+2):
            cost = z3.Real('add_cost_{}'.format(step))
            total = []
            for a,v in self.auxiliary_actions[step].items():
                if len(self.ground_problem.quality_metrics) > 0:
                    total.append(z3.If(v,1.0*sum(self.final_costs[a]),0.0))
                else:
                    total.append(z3.If(v,1.0,0.0))
            constraints.append(cost == sum(total))
            costs.append(cost)

        constraints = z3.And(constraints)

        return sum(costs), constraints

    def encodeOnlyIfNeeded(self):
        """!
        Enforces that auxiliary variables can be executed only ifall steps before
        the suffix are filled with at least one action.

        @return list of Z3 constraints.
        """

        c = []

        for step in range(self.horizon,self.horizon+2):
            rel_a = list(self.auxiliary_actions[step].values())
            actions = []
            for index in range(self.horizon):
                actions.append(z3.Or(list(self.action_variables[index].values())))
            c.append(z3.Implies(z3.Or(rel_a), z3.And(actions)))

        return c

    def encodeRelaxedActions(self):
        """!
        Encodes relaxed universal axioms.

        @return relax: list of Z3 formulas
        """

        # dictionary used to store variables corresponding to concrete costs
        # at last step n
        self.final_costs = defaultdict(list)

        # list of relaxed universal axioms
        relax = []
        step = self.horizon

        for action in self.ground_problem.actions:
            # Append preconditions
            for pre in action.preconditions:
                precondition = inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
                relax.append(z3.Implies(self.auxiliary_actions[step][action.name], precondition))

            # Append effects.
            for effect in action.effects:
                if str(effect.fluent) in self.touched_variables:
                    relax.append(z3.Implies(self.auxiliary_actions[step][action.name], self.touched_variables[str(effect.fluent)]))

        return relax

    def encodeASAP(self):
        """!
        Encodes constraints that push execution of actions as early as possible.

        @return list of Z3 formulas.
        """
        # ASAP constraint are enforced both for concrete and relaxed actions
        all_actions  = self.action_variables.copy()
        all_actions.update(self.auxiliary_actions)

        c = []

        for step in range(self.horizon+1):
            for action in self.ground_problem.actions:
                # Condition 1: action already executed at
                # previous step
                act_pre = all_actions[step][action.name]

                # Condition 2: one of the prec of action was violated
                violated = []

                # Append preconditions
                for pre in action.preconditions:
                    precondition = inorderTraverse(pre, self.problem_z3_variables, step, self.problem_constant_numerics)
                    violated.append(z3.Not(precondition))

                # Condition 3: a mutex was executed a previous step
                # return all actions that are in mutex with the
                # current action
                mutex = [(lambda t:  t[1] if t[0] == action else t[0])(t) for t in self.modifier.mutexes if action in t]
                # fetch action variable
                mutex_vars = [all_actions[step][a.name] for a in mutex]

                # ASAP constraint
                act_post = all_actions[step+1][action.name]
                c.append(z3.Implies(act_post, z3.Or(act_pre, z3.Or(violated), z3.Or(mutex_vars))))

        return c

    def encodeTransitiveClosure(self):
        """!
        Encodes computation of transitive closure at step n+1  (see related paper).

        @return trac: Z3 formulas that encode computation of transitive closure.
        """
        trac = []
        step = self.horizon+1

        for action in self.ground_problem.actions:
            # Append preconditions
            for pre in action.preconditions:
                touched_vars = []
                for var in FreeVarsExtractor().get(pre):
                    if str(var) in self.touched_variables:
                        touched_vars.append(self.touched_variables[str(var)])
                precondition = inorderTraverse(pre, self.problem_z3_variables, step-1, self.problem_constant_numerics)
                trac.append(z3.Implies(self.auxiliary_actions[step][action.name], z3.Or(precondition, z3.Or(touched_vars))))

            # Append effects.
            for effect in action.effects:
                if str(effect.fluent) in self.touched_variables:
                    trac.append(z3.Implies(self.auxiliary_actions[step][action.name], self.touched_variables[str(effect.fluent)]))

        sentinel = object()
        # Encode frame axioms for boolean fluents
        for fluent in self.all_problem_fluents:
            if fluent.type.is_bool_type():
                # Encode frame axioms only if atoms have SMT variables associated
                action_eff = []
                for action in self.ground_problem.actions:
                    effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]

                    for ele in effects_fluents:
                        if str(ele.fluent) == str(fluent):
                            if ele.value.is_true():
                                action_eff.append(self.auxiliary_actions[step][action.name])
                                action_eff.append(self.auxiliary_actions[step-1][action.name])
                            else:
                                action_eff.append(self.auxiliary_actions[step][action.name])
                                action_eff.append(self.auxiliary_actions[step-1][action.name])
                trac.append(z3.Implies(self.touched_variables[str(fluent)], z3.Or(action_eff)))

            elif fluent.type.is_int_type() or fluent.type.is_real_type():
                action_num = []
                for action in self.ground_problem.actions:
                    effects_fluents = [effect for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()]
                    for ele in effects_fluents:
                        if str(ele.fluent) == str(fluent):
                            action_num.append(self.auxiliary_actions[step][action.name])
                            action_num.append(self.auxiliary_actions[step-1][action.name])
                trac.append(z3.Implies(self.touched_variables[str(fluent)], z3.Or(action_num)))
            else:
                raise Exception("Unknown fluent type {}".format(fluent.type))

        return trac

    def _expr_to_z3(self, expr, t, c=None):
            """
            Traverses a tree expression in-order and converts it to a Z3 expression.
            expr: The tree expression node. (Can be a value, variable name, or operator)
            t: The timestep for the Fluents to be considered 
            c: A context manager, as we need to take into account parameters from actions, fluents, etc ...
            Returns A Z3 expression or Z3 value.
            """
            if isinstance(expr, int): # A python Integer
                return z3.IntVal(expr, ctx=self.ctx)
            elif isinstance(expr, bool): # A python Boolean
                return z3.BoolVal(expr, ctx=self.ctx)

            elif isinstance(expr, Effect): # A UP Effect
                eff = None
                if expr.kind == EffectKind.ASSIGN:
                    eff = self._expr_to_z3(expr.fluent, t + 1, c) == self._expr_to_z3(expr.value, t, c)
                if expr.kind == EffectKind.DECREASE:
                    eff = self._expr_to_z3(expr.fluent, t + 1, c) == self._expr_to_z3(expr.fluent, t, c) - self._expr_to_z3(expr.value, t, c)
                if expr.kind == EffectKind.INCREASE:
                    eff = self._expr_to_z3(expr.fluent, t + 1, c) == self._expr_to_z3(expr.fluent, t, c) + self._expr_to_z3(expr.value, t, c)
                if expr.is_conditional():
                    return z3.Implies(self._expr_to_z3(expr.condition, t, c) , eff)
                else:
                    return eff

            elif isinstance(expr, FNode): # A UP FNode ( can be anything really )
                if expr.is_object_exp(): # A UP object
                    raise ValueError(f"{expr} should not be evaluated")
                elif expr.is_constant(): # A UP constant
                    return expr.constant_value()
                elif expr.is_or():  # A UP or
                    return z3.Or([self._expr_to_z3(x, t, c) for x in expr.args])
                elif expr.is_and():  # A UP and
                    return z3.And([self._expr_to_z3(x, t, c) for x in expr.args])
                elif expr.is_fluent_exp(): # A UP fluent
                    return self.up_fluent_to_z3[str_repr(expr)][t]
                elif expr.is_parameter_exp():
                    raise ValueError(f"{expr} should not be evaluated")
                elif expr.is_lt():
                    return self._expr_to_z3(expr.args[0], t, c) < self._expr_to_z3(expr.args[1], t, c)
                elif expr.is_le():
                    return self._expr_to_z3(expr.args[0], t, c) <= self._expr_to_z3(expr.args[1], t, c)
                elif expr.is_times():
                    return self._expr_to_z3(expr.args[0], t, c) * self._expr_to_z3(expr.args[1], t, c)
                elif expr.is_plus():
                    return z3.Sum([self._expr_to_z3(x, t, c) for x in expr.args])
                elif expr.is_minus():
                    return self._expr_to_z3(expr.args[0], t, c) - self._expr_to_z3(expr.args[1], t, c)
                else:
                    raise TypeError(f"Unsupported expression: {expr} of type {type(expr)}")
            else:
                raise TypeError(f"Unsupported expression: {expr} of type {type(expr)}")

    def encode(self,horizon):
        """!
        Builds OMT encoding.

        @param horizon: horizon for bounded planning formula.
        @return formula: dictionary containing subformulas.
        """

        self.horizon = horizon

        # set the planner name.
        self.name = "omt"

        # Create variables
        self.create_variables(horizon+1)

        # Start encoding formula
        formula = defaultdict(list)

        # Encode initial state axioms
        formula['initial'] = self.encode_initial_state()

        # Encode universal axioms
        formula['actions'] = self.encode_actions()

        # Encode explanatory frame axioms
        formula['frame'] = self.encode_frame()

        # Encode execution semantics (lin/par)
        formula['sem'] = self.encode_execution_semantics()

        #
        # Encode relaxed suffix
        #

        # Remove this for now.
        self.var_objective = parseMetric(self)

        # Create auxiliary variables
        self.createAuxVariables()

        # Encode objective function
        formula['objective'] = self.encodeObjective()

        # Encode relaxed transition T^R
        formula['tr'] = self.encodeRelaxedActions()

        # Encode transitive closure
        formula['tc'] = self.encodeTransitiveClosure()

        # Encode ASAP constraints
        formula['asap'] = self.encodeASAP()

        # Encode relaxed  goal state axioms
        goal = self.encode_goal_state()
        formula['real_goal'] = z3.And(goal)
        abstract_goal = self.encodeRelaxedGoal()
        formula['goal'] = z3.Or(z3.And(goal),abstract_goal)

        # Encode loop formula
        formula['lf'] = encodeLoopFormulas(self) # This needs to be fixed.

        # Encode additional cost for relaxed actions
        add_objective, add_constraints = self.encodeAdditionalCosts()
        formula['objective'] = formula['objective'] + add_objective
        formula['additional_constraints'] = add_constraints

        # Perform relaxed actions only if previous steps are filled
        formula['oin'] = self.encodeOnlyIfNeeded()

        return formula

class EncoderSequentialOMT(EncoderOMT):
    """
    Class that encodes a problem to a classical sequential encoding to SMT
    """
    def __init__(self, task):
        super().__init__(task, LinearModifier())
        self.name = "SequentialOMT"  # set the planner name.

class EncoderParallelOMT(EncoderOMT):
    """
    Class that encodes a problem to a parallel encoding to SMT using the forall-step semantics
    TODO: Check this is really forall-step semantics
    """
    def __init__(self, task):
        super().__init__(task, ParallelModifier(True))
        self.name = "ForallOMT"  # set the planner name.

    