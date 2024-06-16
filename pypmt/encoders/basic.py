import z3

from copy import deepcopy
from collections import defaultdict

from unified_planning.shortcuts import Compiler, CompilationKind
from unified_planning.shortcuts import Effect, EffectKind
from unified_planning.shortcuts import FNode

from unified_planning.plans import SequentialPlan
from unified_planning.plans import ActionInstance

from pypmt.encoders.base import Encoder
from pypmt.encoders.utilities import str_repr, remove_delete_then_set
from pypmt.modifiers.modifierLinear import LinearModifier
from pypmt.modifiers.modifierParallel import ParallelModifier

from pypmt.planner.plan.smt_sequential_plan import SMTSequentialPlan

class EncoderGrounded(Encoder):
    """!
    As its filename implies, it's the most basic encoding you can imagine.  It
    first uses UP to ground the problem, and then implements a state-based
    encoding of Planning as SAT.  Details of the encoding can be found in the
    recent Handbooks of Satisfiability in the chapter written by Rintanen:
    Planning and SAT.

    The classical way of improving the performance of encodings is to allow more
    than one action per step (layer). This class is really a "base class" for 
    two encodings:
        - sequential encoding: Kautz & Selman 1992 for the original encoding
        - ForAll semantics: this implements a generalisation for numeric
        planning of the original work in Kautz & Selman 1996 
    """

    def __init__(self, name, task, modifier):
        self.task = task # The UP problem
        self.name = name
        self.modifier = modifier
        self.ctx = z3.Context() # The context where we will store the problem

        self.compilation_results = self._ground() # store the compilation results
        self.grounding_results   = self.compilation_results[-1] # store the grounded UP results
        self.ground_problem      = self.grounding_results.problem  # The grounded UP problem

        # The main idea here is that we have lists representing
        # the layers (steps) containing the respective variables

        # this is a mapping from the UP ground actions to z3 and back
        self.z3_actions_to_up = dict() # multiple z3 vars point to one grounded fluent
        self.up_actions_to_z3 = defaultdict(list)
        
        # mapping from up fluent to Z3 var
        self.up_fluent_to_z3 = defaultdict(list) 

        # frame index, indexing what actions can modify which fluent
        self.frame_add = defaultdict(list)
        self.frame_del = defaultdict(list)
        self.frame_num = defaultdict(list)

        # Store the "raw" formula that we will later instantiate
        self.formula  = defaultdict(list) 

        # Store the length of the formula
        self.formula_length = 0

    def __iter__(self):
        return iter(self.ground_problem.actions)
    
    def __len__(self):
        return self.formula_length

    def get_action_var(self, name, t):
        """!
        Given a str representation of a fluent/action and a timestep,
        returns the respective Z3 var.

        @param name: str representation of a fluent or action
        @param t: the timestep we are interested in
        @returns: the corresponding Z3 variable
        """
        return self.up_actions_to_z3[name][t]

    # TODO: should we consider fixing the grounder to use? Now this would
    # depend on the installation of UP and what is available.
    def _ground(self):
        """! 
        Removes quantifiers from the UP problem via the QUANTIFIERS_REMOVING 
        compiler and then grounds the problem using an available UP grounder
        """
        with Compiler(problem_kind = self.task.kind, 
            compilation_kind = CompilationKind.QUANTIFIERS_REMOVING) as quantifiers_remover:
            qr_result  = quantifiers_remover.compile(self.task, CompilationKind.QUANTIFIERS_REMOVING)

        with Compiler(problem_kind = qr_result.problem.kind, 
            compilation_kind = CompilationKind.CONDITIONAL_EFFECTS_REMOVING) as grounder:
            cer_result = grounder.compile(qr_result.problem, CompilationKind.CONDITIONAL_EFFECTS_REMOVING)

        with Compiler(problem_kind = cer_result.problem.kind, 
            compilation_kind = CompilationKind.GROUNDING) as grounder:
            gr_result = grounder.compile(cer_result.problem, CompilationKind.GROUNDING)
        return (qr_result, cer_result, gr_result)
        
    def _populate_modifiers(self):
        """!
        Populates an index on which grounded actions can modify which fluents. 
        These are used afterwards for encoding the frame.
        """
        for action in self.ground_problem.actions:
            str_action = str_repr(action)
            for effect in action.effects:
               var_modified = str_repr(effect.fluent)
               if effect.value.is_true(): # boolean effect
                   self.frame_add[var_modified].append(str_action)
               elif effect.value.is_false():
                   self.frame_del[var_modified].append(str_action)
               else: # is a numeric or complex expression
                   self.frame_num[var_modified].append(str_action)

    def extract_plan(self, model, horizon):
        """!
        Given a model of the encoding generated by this class and its horizon,
        extract a plan from it.
        @returns: an instance of a SMTSequentialPlan
        """
        plan = SequentialPlan([])
        if not model: return plan
        ## linearize partial-order plan
        for t in range(0, horizon+1):
            for action in self:
                if z3.is_true(model[self.up_actions_to_z3[action.name][t]]):
                        plan.actions.append(ActionInstance(action))
        
        for compilation_r in reversed(self.compilation_results):
            plan = plan.replace_action_instances(compilation_r.map_back_action_instance)

        return SMTSequentialPlan(plan, self.task)

    def encode(self, t):
        """!
        Builds and returns the formulas for a single transition step (from t to t+1).
        @param t: the current timestep we want the encoding for
        @returns: A dict with the different parts of the formula encoded
        """
        if t == 0:
            self.base_encode()
            return deepcopy(self.formula)
        
        self.create_variables(t+1) # we create another layer

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
 
        encoded_formula = dict()
        encoded_formula['initial'] = self.formula['initial'] # TODO not needed?
        encoded_formula['goal']    = z3.substitute(self.formula['goal'], list_substitutions)
        encoded_formula['actions'] = z3.substitute(self.formula['actions'], list_substitutions)
        encoded_formula['frame']   = z3.substitute(self.formula['frame'], list_substitutions)
        encoded_formula['sem']     = z3.substitute(self.formula['sem'], list_substitutions)
        return encoded_formula

    def base_encode(self):
        """!
        Builds the encoding. Populates the formula dictionary class attribute,
        where all the "raw" formulas are stored. Those will later be used by 
        the encode function.
        """
        # create vars for first transition
        self.create_variables(0)
        self.create_variables(1)
        self._populate_modifiers() # do indices

        self.formula['initial'] = z3.And(self.encode_initial_state())  # Encode initial state axioms
        self.formula['goal']    = z3.And(self.encode_goal_state(0))  # Encode goal state axioms
        self.formula['actions'] = z3.And(self.encode_actions(0))  # Encode universal axioms
        self.formula['frame']   = z3.And(self.encode_frame(0))  # Encode explanatory frame axioms
        self.formula['sem']     = z3.And(self.encode_execution_semantics())  # Encode execution semantics (lin/par)

    def encode_execution_semantics(self):
        """!
        Encodes execution semantics as specified by the modifier class held.

        @returns: axioms that specify execution semantics.
        """
        action_vars = list(map(lambda x: x[0], self.up_actions_to_z3.values()))
        return self.modifier.encode(self, action_vars)

    def create_variables(self, t):
        """!
        Creates state variables needed in the encoding for step t.

        @param t: the timestep
        """
        # increment the formula lenght
        self.formula_length += 1

        # for actions
        for grounded_action in self.ground_problem.actions:
            key   = str_repr(grounded_action)
            keyt  = str_repr(grounded_action, t)
            act_var = z3.Bool(keyt, ctx=self.ctx)
            self.up_actions_to_z3[key].append(act_var)
            self.z3_actions_to_up[act_var] = key

        # for fluents
        grounded_up_fluents = [f for f, _ in self.ground_problem.initial_values.items()]
        for grounded_fluent in grounded_up_fluents:
            key  = str_repr(grounded_fluent)
            keyt = str_repr(grounded_fluent, t)
            if grounded_fluent.type.is_real_type():
                self.up_fluent_to_z3[key].append(z3.Real(keyt, ctx=self.ctx))
            elif grounded_fluent.type.is_bool_type():
                self.up_fluent_to_z3[key].append(z3.Bool(keyt, ctx=self.ctx))
            else:
                raise TypeError

    def encode_initial_state(self):
        """!
        Encodes formula defining initial state
        @returns: Z3 formula asserting initial state
        """
        t = 0
        initial = []
        for FNode, initial_value in self.ground_problem.initial_values.items():
            fluent = self._expr_to_z3(FNode, t)
            value  = self._expr_to_z3(initial_value, t)
            initial.append(fluent == value)
        
        return initial

    # TODO: remove t, as it is not needed
    def encode_goal_state(self, t):
        """!
        Encodes formula defining goal state

        @param t: the timestep
        @returns: Z3 formula asserting propositional and numeric subgoals
        """
        goal = []
        for goal_pred in self.ground_problem.goals:
            goal.append(self._expr_to_z3(goal_pred, t + 1))
        return goal

    # TODO: remove t, as it is not needed
    def encode_actions(self, t):
        """!
        Encodes the transition function. That is, the actions.
        a -> Pre
        a -> Eff

        @param t: the timestep
        @returns: list of Z3 formulas asserting the actions
        """
        actions = []
        for grounded_action in self.ground_problem.actions:
            key = str_repr(grounded_action)
            action_var = self.up_actions_to_z3[key][t]

            # translate the action precondition
            action_pre = []
            for pre in grounded_action.preconditions:
                action_pre.append(self._expr_to_z3(pre, t))
            # translate the action effect
            action_eff = []
            for eff in grounded_action.effects:
               action_eff.append(self._expr_to_z3(eff, t))
            # remove any delete-then-set/set-then-delete semantics
            action_eff = remove_delete_then_set(action_eff)

            # the proper encoding
            action_pre = z3.And(action_pre) if len(action_pre) > 0 else z3.BoolVal(True, ctx=self.ctx)
            actions.append(z3.Implies(action_var, action_pre, ctx=self.ctx))
            action_eff = z3.And(action_eff) if len(action_eff) > 0 else z3.BoolVal(True, ctx=self.ctx)
            actions.append(z3.Implies(action_var, action_eff, ctx=self.ctx))
        return z3.And(actions)

    # TODO: remove t, as it is not needed
    def encode_frame(self, t):
        """!
        Encodes the explanatory frame axiom

        basically for each fluent, to change in value it means
        that some action that can make it change has been executed
        f(x,y,z, t) != f(x,y,z, t+1) -> a \/ b \/ c
        """
        frame = [] # the whole frame

        # for each grounded fluent, we say its different from t to t + 1
        grounded_up_fluents = [f for f, _ in self.ground_problem.initial_values.items()]
        for grounded_fluent in grounded_up_fluents:
            key    = str_repr(grounded_fluent)
            var_t  = self.up_fluent_to_z3[key][t]
            var_t1 = self.up_fluent_to_z3[key][t + 1]

            # for each possible modification
            or_actions = []
            or_actions.extend(self.frame_add[key])
            or_actions.extend(self.frame_del[key])
            or_actions.extend(self.frame_num[key])

            # simplify the list in case its empty
            if len(or_actions) == 0:
                who_can_change_fluent = z3.BoolVal(False, ctx=self.ctx)
            else:
                who_can_change_fluent = z3.Or([self.up_actions_to_z3[x][t] for x in or_actions])

            frame.append(z3.Implies(var_t != var_t1, who_can_change_fluent, ctx=self.ctx))
        return frame

    def _expr_to_z3(self, expr, t, c=None):
        """!
        Traverses a UP AST in in-order and converts it to a Z3 expression.
        @param expr: The tree expression node. (Can be a value, variable name, or operator)
        @param t: The timestep for the Fluents to be considered 
        @param c: The context, which can be used to take into account free params
        @returns: An equivalent Z3 expression
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
                return z3.Implies(self._expr_to_z3(expr.condition, t, c) , eff, ctx=self.ctx)
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
            elif expr.is_div():
                return self._expr_to_z3(expr.args[0], t, c) / self._expr_to_z3(expr.args[1], t, c)
            elif expr.is_plus():
                return z3.Sum([self._expr_to_z3(x, t, c) for x in expr.args])
            elif expr.is_minus():
                return self._expr_to_z3(expr.args[0], t, c) - self._expr_to_z3(expr.args[1], t, c)
            elif expr.is_not():
                return z3.Not(self._expr_to_z3(expr.args[0], t, c))
            elif expr.is_equals():
                return self._expr_to_z3(expr.args[0], t, c) == self._expr_to_z3(expr.args[1], t, c)
            elif expr.is_implies():
                return z3.Implies(self._expr_to_z3(expr.args[0], t, c), self._expr_to_z3(expr.args[1], t, c))
            else:
                raise TypeError(f"Unsupported expression: {expr} of type {type(expr)}")
        else:
            raise TypeError(f"Unsupported expression: {expr} of type {type(expr)}")

class EncoderSequential(EncoderGrounded):
    """
    Implementation of the classical sequential encoding of Kautz & Selman 1992
    where each timestep can have exactly one action.
    """
    def __init__(self, task):
        super().__init__("seq", task, LinearModifier())


class EncoderForall(EncoderGrounded):
    """
    Implementation of a generalisation for numeric planning of the original work
    in Kautz & Selman 1996 
    """
    def __init__(self, task):
        super().__init__("seqForall", task, ParallelModifier())
