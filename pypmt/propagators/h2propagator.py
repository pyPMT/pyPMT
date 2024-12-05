import z3
import itertools
from pypmt.encoders.utilities import var_components, str_repr
from typing import List, Dict
from collections import defaultdict

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
        self.verbose = False

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
        self.state_state: List[Dict[str, str]] = []
        # number of fixed variables per timestep
        self.counter: List[int] = []

        self.action_pre = defaultdict(list) # given an action, return the list of preconditions
        self.action_add = defaultdict(list) # given an action, return the list of add effects
        self.action_del = defaultdict(list) # given an action, return the list of del effects
        self.action_num = defaultdict(list) # given an action, return the list of numeric variables changed
        self.create_indices() # fill the dictionaries

        self.last_timestep = 0          # the greatest timestep seen
        self.goal_predicates = set()    # a set of predicates in the goal, assuming STRIPS
        self.preprocess_goals()        # fill the goal_predicates set
        
        self.flag_esperem_conflicte=False

        # debug
        self.printed_step = []

    def preprocess_goals(self):
        for goal in self.encoder.task.goals:
            if goal.is_and():
                for x in goal.args:
                    self.goal_predicates.add(x) 
            else:
                # MEEEC
                pass
    
    def _decide(self, t, var, phase):
        varname, timestep = var_components(t)
        if varname in self.encoder.up_actions_to_z3.keys():
            if self.verbose:
                print(f"we tell the solver to decide on action {t} to be true!")
            self.next_split(t,0,1)

    def push(self): # type: ignore
        # mark a new decision level in the trail.
        self.decision_levels.append(len(self.trail))
        if self.verbose:
            print("pushed decision level")
        if self.flag_esperem_conflicte:
            self.flag_esperem_conflicte=False
            print(f"No hi ha conflicte, decisio nivell {len(self.decision_levels)}")

    # -- Backjumping --
    def pop(self, num_scopes) -> None: # type: ignore
        if self.verbose:
            print(f"popped decision level: {num_scopes} scopes")
        # head is the position of the trail that we have to backtrack to
        head = self.decision_levels[len(self.decision_levels) - num_scopes]
        # while we have not reached the head, undo the last action
        while len(self.trail) > head:
            x = self.trail[-1]
            varname, timestep = var_components(x)
            self.state_state[timestep][varname] = ""
            self.counter[timestep] -= 1
            self.trail.pop()

        self.decision_levels = self.decision_levels[:-num_scopes]
        if self.flag_esperem_conflicte:
            self.flag_esperem_conflicte=False
            print(f"Hi ha conflicte a {len(self.decision_levels)}")

    def _fixed(self, x, v):
        """
        We check if a variable is from the state and we store it.
        """
        # Implement logic for when a variable is fixed to a value
        varname, timestep = var_components(x)

        # this is a state variable
        if varname in self.encoder.up_fluent_to_z3.keys():
            self.state_state[timestep][varname] = v
            self.counter[timestep]+=1
            self.trail.append(x)
            if(self.is_state_defined(timestep)):
                self.compute_heuristic(timestep)

    
    def compute_heuristic(self, timestep):
        #heuristic = self.compute_goal_count(timestep)
        heuristic = self.compute_hm(2,timestep)
        
        if heuristic > self.last_timestep - timestep:
            print(f"Hauriem de fer conflicte aqui: {len(self.decision_levels)}")
            self.flag_esperem_conflicte=True

        if not self.printed_step[timestep]:
            if self.verbose:
                self.print_state(timestep)
            self.printed_step[timestep] = True

    def compute_hm(self, m, timestep):
        def regression(goal, action):
            if len(goal.intersection(self.action_add[action]))==0 or \
            len(goal.intersection(self.action_del[action]))!=0:
                return -1
            return (goal.difference(self.action_add[action])).union(self.action_pre[action])

        def compute_hm_(m, timestep, goal):
            # if the goal is already satisfied, return 0. That is, if the goal is a strict subset of the true facts of the state
            s = set([fact for fact in self.state_state[timestep].keys() if self.state_state[timestep][fact]])
            if goal.issubset(s):
                print(f"setbase: 0, {s}")
                return 0
            elif len(goal) <= m:
                entered = False
                min = self.last_timestep
                setmin = set()
                for action in self.encoder.task.actions:
                    r = regression(goal, action)
                    # TODO what would happen if all goals are undefined?
                    # That is, there is no action that can help us reach the goal (regression would always give -1)
                    if r != -1:
                        entered = True
                        hm = compute_hm_(m,timestep,r)
                        if hm < min:
                            (min,setmin) = (hm,r)
                print(f"setmin: {entered} {min} {setmin}")
                return min+1
            else:
                max = -1
                setmax = set()
                for actions_prime in itertools.combinations(goal, m):
                    hm = compute_hm_(m,timestep,set(actions_prime))
                    if hm > max:
                        (max,setmax) = (hm,set(actions_prime))
                print(f"setmax: {max} {setmax}")
                return max
        
        return compute_hm_(m, timestep, self.goal_predicates)


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