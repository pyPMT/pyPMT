import z3
import itertools
from pypmt.encoders.utilities import var_components, str_repr
from typing import List, Dict
from collections import defaultdict
from functools import lru_cache

class H2Propagator(z3.UserPropagateBase):
    """!
    A base class that receives an encoder and implements a custom propagator.
    It already includes the basic structure for a propagator and the trail
    management.
    """

    def __init__(self, encoder, s=None, ctx=None):
        # We need to call the parent constructor for Z3 to do its magic.
        super().__init__(s, ctx)

        # The encoder holds the semantic mappings between UP and Z3 variables.
        self.encoder = encoder

        # The solver holds the actual Z3 solver instance.
        self.solver = s

        # output stuff?
        self.verbose = True

        # keep track of changes/assignments made during the decision process
        # each entry is an action or change that can be undone.
        self.trail = []

        # Not all elements in the trail are decisions. This list that marks
        # decision levels in the previous trail. Here we store the length
        # of the trail at a specific decision level. Helps to identify where
        # to backtrack to when popping decision levels.
        self.decision_levels = []

        # We add the custom fixed and final methods to the propagator
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.add_final(lambda: self._final())
        self.add_decide(lambda t, x, v: self._decide(t, x, v))
        self.encoder = encoder

        # variables that belong to the propagator per se.
        # each entry is a dictionary with the state variables and their value per step
        self.state_state: List[Dict[str, str]] = [{}]
        # number of fixed variables per timestep
        self.counter: List[int] = [0]

        self.action_pre = defaultdict(list) # given an action, return the list of preconditions
        self.action_add = defaultdict(list) # given an action, return the list of add effects
        self.action_del = defaultdict(list) # given an action, return the list of del effects
        self.action_num = defaultdict(list) # given an action, return the list of numeric variables changed
        self.create_indices() # fill the dictionaries

        self.last_timestep = 0          # the greatest timestep seen
        self.goal_predicates = None     # a set of predicates in the goal, assuming STRIPS
        self.preprocess_goals()         # fill the goal_predicates set
        
        self.flag_esperem_conflicte=False

        # size (m) of the combination of goal facts considered by the heuristic h_m
        self.SUBSETSIZE = 2

        # debug
        self.printed_step = []
        self.true_val = z3.BoolVal(True, ctx=self.encoder.ctx)
        self.false_val = z3.BoolVal(False, ctx=self.encoder.ctx)

    def preprocess_goals(self):
        goal_predicates = set()
        for goal in self.encoder.task.goals:
            if goal.is_and():
                for x in goal.args:
                    goal_predicates.add(str_repr(x)) 
            else:
                # MEEEC
                pass
        self.goal_predicates = frozenset(goal_predicates)
    
    def _decide(self, t, var, phase):
        varname, timestep = var_components(t)
        # TODO, first assign the goal literals
        if varname in self.encoder.up_actions_to_z3.keys():
            if self.verbose:
                print(f"we tell the solver to decide on action {t} to be true!")
            self.next_split(t,0,1)

    def push(self): # type: ignore
        # mark a new decision level in the trail.
        self.decision_levels.append(len(self.trail))
        #if self.verbose:
            #print("pushed decision level")
        if self.flag_esperem_conflicte:
            self.flag_esperem_conflicte=False
            print(f"No hi ha conflicte, decisio nivell {len(self.decision_levels)}")

    # -- Backjumping --
    def pop(self, num_scopes) -> None: # type: ignore
        #print(f"popping decision level: {num_scopes} scopes")
        #print("self.decision_levels", self.decision_levels)
        #print(f"trail: {self.trail}")
        #counts = defaultdict(int)

        # head is the position of the trail that we have to backtrack to
        head = self.decision_levels[len(self.decision_levels) - num_scopes]
        # while we have not reached the head, undo the last action
        while len(self.trail) > head:
            x = self.trail[-1]
            varname, timestep = var_components(x)
            self.state_state[timestep][varname] = ""
            self.counter[timestep] -= 1
            self.trail.pop()
            #counts[timestep] += 1

        #print(f"popped levels: {counts}")

        self.decision_levels = self.decision_levels[:-num_scopes]
        if self.flag_esperem_conflicte:
            self.flag_esperem_conflicte=False
            if self.verbose:
                print(f"Hi ha conflicte a {len(self.decision_levels)}")

    def _fixed(self, x, v):
        """
        We check if a variable is from the state and we store it.
        """
        # Implement logic for when a variable is fixed to a value
        varname, timestep = var_components(x)

        #print(f"fixed {x} to {v}")
        # this is a state variable
        if varname in self.encoder.up_fluent_to_z3.keys():
            self.state_state[timestep][varname] = v
            self.counter[timestep] += 1
            self.trail.append(x)

            if(self.is_state_defined(timestep)):
                #print(f"step {timestep} has {self.counter[timestep]}/{len(self.encoder.up_fluent_to_z3.keys())} defined")
                heuristic = self.compute_heuristic(timestep)
                #print(f"heuristic: {heuristic} calculated from step {timestep} and state {self.state_state[timestep]} seen with horizon {self.last_timestep}")
                if heuristic > self.last_timestep - timestep:
                    if self.verbose:
                        print(f"Hauriem de fer conflicte a decision level: {len(self.decision_levels)}")
                    self.flag_esperem_conflicte=True

                    fixed_ids_at_timestep = [] # the literals fixed at the given timestep
                    for str_var, value in self.state_state[timestep].items():
                        z3_var = self.encoder.up_fluent_to_z3[str_var][timestep]
                        fixed_ids_at_timestep.append(z3_var)

                    # add the goal to the conflict
                    lits = []
                    for goal_pred in self.goal_predicates:
                        lits.append(z3.Not(self.encoder.up_fluent_to_z3[str_repr(goal_pred)][self.last_timestep], ctx=self.encoder.ctx))
                    negated_goal = z3.Or(lits)

                    #if self.verbose:
                    #    print(f"pacasa, timestep {timestep} with conflict {literals}")
                    #print(f"state: {self.state_state[timestep]}")
                    print(f"pacasa: propaguem: {negated_goal} with {fixed_ids_at_timestep}")
                    self.propagate(negated_goal, ids=fixed_ids_at_timestep) # let z3 know that there is a conflict
                    
                if not self.printed_step[timestep]:
                    if self.verbose:
                        self.print_state(timestep)
                    self.printed_step[timestep] = True

    
    def compute_heuristic(self, timestep):
        #heuristic = self.compute_goal_count(timestep)
        return self.compute_hm(self.SUBSETSIZE, timestep)
       

    def compute_hm(self, m, timestep):
        @lru_cache(maxsize=None)
        def regression(goal, action):
            str_action = str_repr(action)
            goal_str = frozenset([str_repr(x) for x in goal])
            if len(goal_str.intersection(self.action_add[str_action]))==0 or \
               len(goal_str.intersection(self.action_del[str_action]))!=0:
                return -1
            return (goal_str.difference(self.action_add[str_action])).union(self.action_pre[str_action])

        @lru_cache(maxsize=None)
        def compute_hm_(m, timestep, goal, credit):
            #print(f"crida recursiva amb: m:{m}, step:{timestep} goal:{goal} i credit:{credit}")
            # if the goal is already satisfied, return 0. That is, if the goal is a strict subset of the true facts of the state
            s = frozenset([fact for fact in self.state_state[timestep].keys() if self.state_state[timestep][fact]])
            if goal.issubset(s):
                #print(f"trobat: {goal} is subset of {s}")
                return 0

            # we are further from the bound we have
            if credit == 0:
                #print(f"ens hem quedat sense credit")
                return self.last_timestep + 1 # infinity

            elif len(goal) <= m:
                #print(f"len(goal) <= m: {len(goal)} <= {m}")
                min = self.last_timestep
                setmin = set()
                for action in self.encoder.task.actions:
                    r = regression(goal, action)
                    #print(f"len(goal) <= m: regression: {r}")
                    # That is, there is no action that can help us reach the goal (regression would always give -1)
                    if r != -1:
                        hm = compute_hm_(m, timestep, r, credit-1)
                        if hm < min:
                            (min,setmin) = (hm,r)
                #print(f"len(goal) <= m: return {min+1}")
                return min + 1
            else:
                max = -1
                setmax = set()
                for actions_prime in itertools.combinations(goal, m):
                    hm = compute_hm_(m, timestep, frozenset(actions_prime), credit)
                    if hm > max:
                        (max,setmax) = (hm,frozenset(actions_prime))
                #print(f"len(goal) > m: return {max}")
                return max

        return compute_hm_(m, timestep, self.goal_predicates, self.last_timestep - timestep)


    # returns the number of goals NOT satisfied in the current state
    def compute_goal_count(self, timestep):
        count = 0
        for goal_pred in self.goal_predicates:
            if self.state_state[timestep][str_repr(goal_pred)] == True:
                count += 1
        return len(self.goal_predicates)-count


    def print_state(self,timestep):
        """ print(f"Estat definit al timestep {timestep}")
            for k, v in self.state_state[timestep].items():
                if v:
                    print(f"State variable {k} in timestep {timestep} is {v}")
        """
        print(f"--- Estat al timestep {timestep} ---")
        n_per_linia = 5
        n_printed = 0
        for k, v in self.state_state[timestep].items():
            if v:
                print(f"{k}", end=" ")
                if n_printed % n_per_linia == n_per_linia-1:
                    print()
                n_printed += 1
        print("\n------------------------------------")


    # returns true if all state variables are defined for a given timestep
    def is_state_defined(self, timestep):
        return self.counter[timestep]==len(self.encoder.up_fluent_to_z3.keys())


    def new_timestep(self):
        self.last_timestep += 1
        self.flag_esperem_conflicte = False
        self.printed_step.append(False)
        self.state_state.append({})
        self.counter.append(0)


    def create_indices(self):
        # TODO: fill frame_pre

        for action in self.encoder.task.actions:
            str_action = str_repr(action)

            for pre in action.preconditions:
                self.action_pre[str_action].append(str_repr(pre))
                
            for effect in action.effects:
               var_modified = str_repr(effect.fluent)
               if effect.value.is_true(): # boolean effect
                   self.action_add[str_action].append(var_modified)
               elif effect.value.is_false():
                   self.action_del[str_action].append(var_modified)
               else: # is a numeric or complex expression
                   self.action_num[str_action].append(var_modified)


    def _final(self):
        print("final called")
        pass