from collections import Counter
from functools import lru_cache

import z3
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
            s += str(fluent_arg) if fluent_arg.is_variable_exp() else f"_{fluent_arg.constant_value()}"

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

    
def remove_delete_then_set(effects):
    """!
    Removes delete-then-set effects from the list of effects.
    @param effects: list of effects
    @return list of effects without delete-then-set effects
    """
    # collect boolean only effect fluents
    collected_effect_fluents = filter(lambda f:isinstance(f.sort(), z3.z3.BoolSortRef), [e.children()[0] for e in effects])
    # keep fluents with more than one appearance
    deleted_then_set_fluents = list(map(lambda x:x[0], filter(lambda item: item[1] != 1, Counter(collected_effect_fluents).items())))
    # remove delete-then-set effects
    return list(filter(lambda e: not isinstance(e.children()[0].sort(), z3.z3.BoolSortRef) or 
                                 not e.children()[0] in deleted_then_set_fluents, effects))

def flattern_list(list_of_lists):
    return sum((flattern_list(sub) if isinstance(sub, list) else [sub] for sub in list_of_lists), [])