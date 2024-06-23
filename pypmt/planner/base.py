from unified_planning.plans import SequentialPlan
from pypmt.planner.plan.smt_sequential_plan import SMTSequentialPlan
from pypmt.config import config


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
        self.solution   = SMTSequentialPlan(SequentialPlan([]), encoder.task)
        self.propagator = config.get("propagator")
    
    def search(self):
        raise NotImplementedError

    def dump_smtlib_to_file(self, t, path):
        raise NotImplementedError