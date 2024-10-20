from unified_planning.model.problem import Problem
from unified_planning.shortcuts import Compiler, CompilationKind

from unified_planning.io import PDDLReader
from unified_planning.model.fluent import get_all_fluent_exp

from unified_planning.shortcuts import get_environment
from unified_planning.shortcuts import Fraction

from pypmt.encoders.utilities import flattern_list

from pypmt.config import Config
from pypmt.config import global_config  # Import the global configuration

from pypmt.utilities import log

def compile(task: Problem, compilationlist: list):
    """
    Compiles a given task using a specified list of compilation names and kinds.

    Args:
        task (Problem): The UP task to be compiled.
        compilationlist (list): A list of tuples where each tuple contains a name and a kind for compilation.

    Returns:
        CompiledTask: The compiled task object.
    """
    names = [name for name, _ in compilationlist]
    compilationkinds = [kind for _, kind in compilationlist]
    with Compiler(names=names, compilation_kinds=compilationkinds) as compiler:
        compiled_task = compiler.compile(task)
    return compiled_task

def check_compatibility(encoder, compliationlist:list):
    compatible = True
    reason = ['incompatibility reasons:']
    # First check is to know whether the encoder requires grounding or not.
    grounded_encoding = 'EncoderGrounded' in [c.__name__ for c in encoder.__mro__]
    has_grounding = any([kind == CompilationKind.GROUNDING for _, kind in compliationlist])
    has_quantifiers_removal = any([kind == CompilationKind.QUANTIFIERS_REMOVING for _, kind in compliationlist])

    if grounded_encoding and not has_grounding:
        reason.append(f"The {encoder.__name__} requires grounding but the compilation list does not have it.")
    if not grounded_encoding and has_grounding:
        reason.append(f"The {encoder.__name__} does not require grounding but the compilation list has it.")
    if grounded_encoding and not has_quantifiers_removal:
        reason.append(f"The {encoder.__name__} requires quantifiers removal but the compilation list does not have it.")

    compatible = compatible and ((not grounded_encoding and not has_grounding) or (grounded_encoding and has_grounding and has_quantifiers_removal))
    
    return compatible, '\n'.join(reason)

def set_global_config(conf:Config):
    """
    Sets the global configuration object
    Args:
        conf (Config): The configuration object to be set as global.
    """
    global_config.set_config(conf)

def initialize_fluents(task:Problem):
    """
    Initialize the int and real fluents of a given task with a default value of 0.
    Args:
        task (Problem): The UP task object
    Updates:
        task.initial_defaults: Adds default values for real and integer types.
        task.explicit_initial_values: Sets initial values for uninitialized fluents.
    """
    # update the initial defaults to account for real and integer types.
    _env = get_environment()
    _tm = _env.type_manager
    _em = _env.expression_manager
    task.initial_defaults.update({_tm.RealType():_em.Real(Fraction(0))})
    task.initial_defaults.update({_tm.IntType() :_em.Int(0)})

    # list unitialized fluents.
    fluentslist = flattern_list([list(get_all_fluent_exp(task, f)) for f in task.fluents])
    initialized_fluents  = list(task.explicit_initial_values.keys())
    unintialized_fluents = list(filter(lambda x: not x in initialized_fluents, fluentslist))
    
    # update the initial values for the fluents that are not initialized.
    for fe in unintialized_fluents:
        task.set_initial_value(fe, task.initial_defaults[fe.type]) 

def create_encoder(encoder, domainfile:str, problemfile:str, compilationlist:list):
    task = PDDLReader().parse_problem(domainfile, problemfile)
    # initialise the fluents if needed
    initialize_fluents(task)
    # TODO: we need to find a way to validate the compilation list compatibility with the encoder before proceeding.
    compatible, reason = check_compatibility(encoder, compilationlist)
    assert compatible, f"The compilation list is not compatible due to: {reason}"
    # apply compilation list.
    compiled_task = compile(task, compilationlist)
    return encoder(compiled_task.problem), compiled_task

def generate_schedule(conf:Config):
    ub = conf.get("ub")
    return list(range(0, ub))

def solve(domainfile:str, problemfile:str, conf:Config, validate_plan:bool=True):
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
    set_global_config(conf)
    encoder = global_config.get("encoder")
    search_strategy = global_config.get("search")
    compilationlist = global_config.get("compilationlist")

    # create the encoder and run the search
    schedule = generate_schedule(global_config)
    encoder_instance, compiled_task = create_encoder(encoder, domainfile, problemfile, compilationlist)
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

def dump_smtlib(domainfile:str, problemfile:str, conf:Config):
    """!
    Basic entry point to dump a SMTLIB2 file
    """
    set_global_config(conf)
    encoder = global_config.get("encoder")
    search_strategy = global_config.get("search")
    compilationlist = global_config.get("compilationlist")

    output_file = global_config.get("output_file")
    step = global_config.get("encoded_step")

    schedule = generate_schedule(global_config)
    encoder_instance, _ = create_encoder(encoder, domainfile, problemfile, compilationlist)
    # create an instance of the search strategy and dump the generated SMTLIB code
    # TODO: I think this should be done in the encoder and not in the search strategy.
    search_strategy(encoder_instance, schedule).dump_smtlib_to_file(step, output_file)