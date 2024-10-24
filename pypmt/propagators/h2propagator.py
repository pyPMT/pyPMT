import z3
import pypmt.propagators.base as BasePropagator

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

        # keep track of changes/assignments made during the decision process
        # each entry is an action or change that can be undone.
        self.trail = []

        # Not all elements in the trail are decisions. This list that marks
        # decision levels in the previous trail. Here we store the length
        # of the trail at a specific decision level. Helps to identify where
        # to backtrack to when popping decision levels.
        self.decision_levels = []

        # We add the custom fixed and final methods to the propagator
        self.decide = None # fixing Z3?
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.add_decide(lambda x, v: self._decide(x, v))
        self.add_final(lambda: self._final())
        self.encoder = encoder

    def push(self): # type: ignore
        # mark a new decision level in the trail.
        self.decision_levels.append(len(self.trail))
        print("PUTA")

    def pop(self, num_scopes) -> None: # type: ignore
        # head is the position of the trail that we have to backtrack to
        head = self.decision_levels[len(self.decision_levels) - num_scopes]
        # while we have not reached the head, undo the last action
        while len(self.trail) > head:
            self.trail.pop()
        self.decision_levels = self.decision_levels[:-num_scopes]

    def _fixed(self, x, v):
        # Implement logic for when a variable is fixed to a value
        # print(f"fixed {x} to {v}")
        pass

    def _decide(self, x, v):
        print(f"decided on {x} to {v}")

    def _final(self):
        # Implement final check logic
        pass