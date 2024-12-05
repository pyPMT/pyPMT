import z3
from pypmt.encoders.utilities import var_components
from typing import List, Dict

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
        self.state_state: List[Dict[str, str]]
        self.counter: List[int]
    
    def _decide(self, t, var, phase):
        varname, timestep = var_components(t)
        if varname in self.encoder.up_actions_to_z3.keys():
            print(f"changed action variable {t} to be true!")
            self.next_split(t,0,1)

    def push(self): # type: ignore
        # mark a new decision level in the trail.
        self.decision_levels.append(len(self.trail))
        if self.verbose:
            print("pushed decision level")

    # -- Backjumping --
    def pop(self, num_scopes) -> None: # type: ignore
        if self.verbose:
            print(f"popped decision level: {num_scopes} scopes")
        # head is the position of the trail that we have to backtrack to
        head = self.decision_levels[len(self.decision_levels) - num_scopes]
        # while we have not reached the head, undo the last action
        while len(self.trail) > head:
            x = self.trail.top()
            varname, timestep = var_components(x)
            self.state_state[timestep][varname] = None
            self.counter[timestep]-=1
            self.trail.pop()

        self.decision_levels = self.decision_levels[:-num_scopes]

    def _fixed(self, x, v):
        """
        We check if a variable is from the state and we store it.
        """
        #(in-city ?loc - place ?city - city)
		#(at ?obj - physobj ?loc - place)
		#(in ?pkg - package ?veh - vehicle))
 
        # Implement logic for when a variable is fixed to a value
        varname, timestep = var_components(x)

        # this is a state variable
        if varname in self.encoder.up_fluent_to_z3.keys():
            print(f"fixed state variable {varname} in timestep {timestep} to {v}")
            self.state_state[timestep][varname] = v
            self.counter[timestep]+=1
            self.trail.push(x)
         

        #if self.verbose:
        #    if varname in self.encoder.up_actions_to_z3.keys():
        #        print(f"fixed action variable {varname} in timestep {timestep} to {v}")
        #    else:
        #        print(f"fixed state variable {varname} in timestep {timestep} to {v}")
    
    def compute_heuristic(self, timestep):
        print("computing heuristic")

    def _final(self):
        print("final called")
        pass