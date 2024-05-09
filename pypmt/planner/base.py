
from pypmt.config import config


class Search:
    """
    Base class defining search schemes.
    """

    def __init__(self, encoder, scheduler, **kwargs):
        self.encoder    = encoder
        self.found      = False
        self.solution   = None
        self.solver     = None
        self.horizon    = None
        self.scheduler  = scheduler
        self.propagator = config.get("propagator")
    
    def search(self):
        raise NotImplementedError

    def dump_smtlib_to_file(self, t, path):
        raise NotImplementedError