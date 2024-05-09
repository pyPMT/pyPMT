
from functools import lru_cache

from unified_planning.shortcuts import InstantaneousAction, FNode

@lru_cache()
def str_repr(f, t=None):
    """! 
    given a FNode from UP representing a fluent and a possible timestep return a
    string representation of it. 
    """
    if isinstance(f, FNode) and f.is_fluent_exp(): # for fluents
        s = f.fluent().name
        # we concatenate the parameters to the name
        for fluent_arg in f.args:
            s += f"_{fluent_arg.constant_value()}"

    elif isinstance(f, InstantaneousAction): # for actions
        s = f.name
        # we concatenate the parameters to the name
        for arg in f.parameters:
            s += f"_{arg.constant_value()}"
    else:
        raise TypeError(f"Unsupported thing: {f} of type {type(f)}")
        
    if t is not None: # and finally the timestep if there is one
        s += f"_{t}"
    return s