from unified_planning.model.problem import Problem
from unified_planning.shortcuts import Compiler, CompilationKind
from unified_planning.engines.results import CompilerResult

from unified_planning.io import PDDLReader
from unified_planning.model.fluent import get_all_fluent_exp


from pypmt.encoders.base import Encoder
from pypmt.encoders.SequentialLifted import EncoderSequentialLifted
from pypmt.encoders.SequentialQFUF import EncoderSequentialQFUF
from pypmt.encoders.OMT import EncoderSequentialOMT
from pypmt.encoders.R2E import EncoderRelaxed2Exists
from pypmt.encoders.basic import EncoderForall, EncoderSequential


from pypmt.planner.SMT import SMTSearch
from pypmt.planner.lifted import LiftedSearch
from pypmt.planner.QFUF import QFUFSearch

from pypmt.shared.valid_configs import valid_configs
from pypmt.encoders.utilities import flattern_list

from pypmt.config import config

from pypmt.utilities import log

def compile(task:Problem, compilationlist:list):
    names = [name for name, _ in compilationlist]
    compilationkinds = [kind for _, kind in compilationlist]
    with Compiler(names=names, compilation_kinds=compilationkinds) as compiler:
        compiled_task = compiler.compile(task)
    return compiled_task

def check_compatibility(encoder:Encoder, compliationlist:list):
    compatible = True
    reason = ['incompatibility reasons:']
    # First check is to know whether the encoder requires grounding or not.
    grounded_encoding = 'EncoderGrounded' in [c.__name__ for c in encoder.__mro__]
    has_grounding = any([kind == CompilationKind.GROUNDING for _, kind in compliationlist])
    has_qunatifiers_removal = any([kind == CompilationKind.QUANTIFIERS_REMOVING for _, kind in compliationlist])

    if grounded_encoding and not has_grounding:
        reason.append(f"The {encoder.__name__} requires grounding but the compilation list does not have it.")
    if not grounded_encoding and has_grounding:
        reason.append(f"The {encoder.__name__} does not require grounding but the compilation list has it.")
    if grounded_encoding and not has_qunatifiers_removal:
        reason.append(f"The {encoder.__name__} requires quantifiers removal but the compilation list does not have it.")

    compatible = compatible and ((grounded_encoding and has_grounding) or (not grounded_encoding and not has_grounding))
    compatible = compatible and ((grounded_encoding and has_qunatifiers_removal) or (not grounded_encoding))
    
    return compatible, '\n'.join(reason)


def initialize_fluents(task:Problem):
    fluentslist = flattern_list([list(get_all_fluent_exp(task, f)) for f in task.fluents])
    initialized_fluents  = list(task.explicit_initial_values.keys())
    unintialized_fluents = list(filter(lambda x: not x in initialized_fluents, fluentslist))
    for fe in unintialized_fluents:
        if fe.type.is_bool_type():
            task.set_initial_value(fe, False) # we need this for plan validator.
        elif fe.type.is_real_type():
            task.set_initial_value(fe, 0) # we need this for plan validator.
        else:
            raise TypeError

def create_encoder(encoder:Encoder, domainfile:str, problemfile:str, compilationlist:list):
    task = PDDLReader().parse_problem(domainfile, problemfile)
    # initialise the fluents
    initialize_fluents(task)
    # TODO: we need to find a way to validate the compilation list compatibility with the encoder before proceeding.
    compatible, reason = check_compatibility(encoder, compilationlist)
    assert compatible, f"The compilation list is not compatible due to the following {reason}"
    # apply compilation list.
    compiled_task = compile(task, compilationlist)
    return encoder(compiled_task.problem), compiled_task

def generate_schedule():
    encoder = config.get("encoder")
    upperbound = config.get("ub")
    return generate_schedule_for(encoder, upperbound)

def generate_schedule_for(encoder, upperbound):
    schedule = None
    # encode
    if encoder in [EncoderSequentialLifted,\
                   EncoderSequentialQFUF, \
                   EncoderSequential,\
                   EncoderForall,\
                   EncoderRelaxed2Exists,\
                   EncoderSequentialOMT]:
        schedule = list(range(0, upperbound))
    else:
        raise Exception(f"Unknown encoder {encoder}")
    return schedule

def solve(domainfile:str, problemfile:str, config_name:str=None, compilationlist:list=None, validate_plan:bool=True):
    """!
    Basic entry point to start searching
    Beforehand the config has to be set by doing for example:

    from pypmt.config import config
    from pypmt.encoders.basic import EncoderSequential
    from pypmt.planner.SMT import SMTSearch

    or passing them as parameters:
    from pypmt.apis import solve
    from unified_planning.shortcuts import CompilationKind
    sol = solve(domainfile, problemfile, "qfuf", []) 
    sol = solve(domainfile, problemfile, "seq",  [('up_grounder', CompilationKind.GROUNDING)])
    """
    if config_name is not None:
        config.set("encoder",         valid_configs[config_name][0])
        config.set("search",          valid_configs[config_name][1])
        config.set("compilationlist", valid_configs[config_name][2] if compilationlist is None else compilationlist)

    encoder = config.get("encoder")
    assert encoder is not None, "Encoder not set"

    compilationlist = config.get("compilationlist")
    assert compilationlist is not None, "Compilation list not set"

    schedule = generate_schedule()
    encoder_instance, compiled_task = create_encoder(encoder, domainfile, problemfile, compilationlist)

    # search
    search_strategy = config.get("search")
    plan = search_strategy(encoder_instance, schedule).search()
    # validate plan if there is a plan and we're asked to
    if plan and validate_plan:
        plan.validate()
        # lift the plan to it's original task.
        plan.plan = plan.plan.replace_action_instances(compiled_task.map_back_action_instance)
        
    if plan is None:
        log('No solution found', 1)
        return None
    elif plan.isvalid:
        log('The plan is valid', 1)
        log(plan, 1)
        return plan
    else:
        log('The plan is invalid!', 1)
        return None

def dump_smtlib(domainfile:str, problemfile:str, path:str, bound=None, config_name=None, compilationlist=None):
    """!
    Basic entry point to dump a SMTLIB2 file
    """
    if config_name is not None:
        config.set("encoder",         valid_configs[config_name][0])
        config.set("search",          valid_configs[config_name][1])
        config.set("compilationlist", valid_configs[config_name][2] if compilationlist is None else compilationlist)

    encoder = config.get("encoder")
    compilationlist = config.get("compilationlist")

    if bound is None: # get the bound we want
        bound = config.get("ub")

    assert encoder is not None, "Encoder not set!"
    schedule = generate_schedule()
    encoder_instance, _ = create_encoder(encoder, domainfile, problemfile, compilationlist)
    search_strategy = config.get("search")
    # create an instance of the search strategy and dump the generated SMTLIB code
    search_strategy(encoder_instance, schedule).dump_smtlib_to_file(bound, path)