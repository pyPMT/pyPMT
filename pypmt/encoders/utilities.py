from collections import Counter
from functools import lru_cache

import z3
from unified_planning.shortcuts import InstantaneousAction, FNode, OperatorKind

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
            match fluent_arg.node_type:
                case OperatorKind.VARIABLE_EXP:
                    s += str(fluent_arg)
                case OperatorKind.NOT:
                    s += str_repr(fluent_arg.args[0])
                case _:
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

@lru_cache()
def varstr_repr(var):
    """! 
    given a z3 variable return the variable name. 
    """
    varname = str(var)
    return varname[:varname.rfind('_')]

def flattern_list(list_of_lists):
    return sum((flattern_list(sub) if isinstance(sub, list) else [sub] for sub in list_of_lists), [])