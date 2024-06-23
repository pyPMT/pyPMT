from unified_planning.plans import SequentialPlan
from pypmt.config import config
from pypmt.planner.plan.smt_sequential_plan import SMTSequentialPlan


class Search:
    """
    Base class defining search schemes.
    """

    def __init__(self, encoder, scheduler, **kwargs):
        self.encoder    = encoder
        self.found      = False
        self.solver     = None
        self.horizon    = None
        self.scheduler  = scheduler
        self.solution   = SMTSequentialPlan(SequentialPlan([]), None)
        self.propagator = config.get("propagator")
    
    def search(self):
        raise NotImplementedError

    def dump_smtlib_to_file(self, t, path):
        raise NotImplementedError