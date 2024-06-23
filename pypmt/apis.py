import unified_planning as up
from unified_planning.io import PDDLReader
from unified_planning.shortcuts import Compiler, CompilationKind

from pypmt.encoders.R2E import EncoderRelaxed2Exists
from pypmt.encoders.basic import EncoderForall, EncoderSequential

from pypmt.encoders.base import Encoder
from pypmt.encoders.SequentialLifted import EncoderSequentialLifted
from pypmt.encoders.SequentialQFUF import EncoderSequentialQFUF

from pypmt.planner.SMT import SMTSearch
from pypmt.planner.lifted import LiftedSearch
from pypmt.planner.QFUF import QFUFSearch

from pypmt.shared.valid_configs import valid_configs

from pypmt.config import config

from pypmt.utilities import log


def create_encoder(encoder:Encoder, compilation_seq, domainfile:str, problemfile:str):
    task = PDDLReader().parse_problem(domainfile, problemfile)

    compiled_tasks = [task]
    for name, compilation_kind in compilation_seq:
        args = {}
        if name: args['name'] = name
        args['compilation_kind'] = compilation_kind
        _task = compiled_tasks[-1] if 'kind' in dir(compiled_tasks[-1]) else compiled_tasks[-1].problem
        with Compiler(**args, problem_kind = _task.kind) as compiler:
            compiled_tasks.append(compiler.compile(_task, compilation_kind))

    return encoder(compiled_tasks)

def generate_schedule():
    encoder = config.get("encoder")
    upperbound = config.get("ub")
    return generate_schedule_for(encoder, upperbound)

def generate_schedule_for(encoder, upperbound):
    schedule = None
    # encode
    if encoder in [EncoderSequentialLifted, EncoderSequentialQFUF, \
                    EncoderSequential, EncoderForall, EncoderRelaxed2Exists]:
        schedule = list(range(0, upperbound))
    else:
        raise Exception(f"Unknown encoder {encoder}")
    return schedule

def solve(domainfile:str, problemfile:str, config_name=None, compilation_seq=[], validate_plan=True):
    """!
    Basic entry point to start searching
    Beforehand the config has to be set by doing for example:

    from pypmt.config import config
    from pypmt.encoders.basic import EncoderSequential
    from pypmt.planner.SMT import SMTSearch

    or passing them as parameters:
    from pypmt.apis import solve

    # compilation_seq is a list of tuples where the first element is the name of the compilation 
    # and the second element is the kind of compilation.

    compilation_seq = [('up_grounder', CompilationKind.GROUNDING), 
                       (None, CompilationKind.QUANTIFIERS_REMOVING)]

    solve(domainfile, problemfile, "qfuf", compilation_seq) 
    """
    if config_name is not None:
        config.set("encoder", valid_configs[config_name][0])
        config.set("search", valid_configs[config_name][1])

    encoder = config.get("encoder")
    assert encoder is not None, "Encoder not set"
    schedule = generate_schedule()
    encoder_instance = create_encoder(encoder, compilation_seq, domainfile, problemfile)

    # search
    search_strategy = config.get("search")
    plan = search_strategy(encoder_instance, schedule).search()
    
    # validate plan if there is a plan and we're asked to
    if validate_plan and plan:
        plan.validate()
    
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
    

def dump_smtlib(domainfile:str, problemfile:str, path:str, bound=None, config_name=None):
    """!
    Basic entry point to dump a SMTLIB2 file
    """
    if config_name is not None:
        config.set("encoder", valid_configs[config_name][0])
        config.set("search", valid_configs[config_name][1])

    encoder = config.get("encoder")

    if bound is None: # get the bound we want
        bound = config.get("ub")

    assert encoder is not None, "Encoder not set!"
    schedule = generate_schedule()
    encoder_instance = create_encoder(encoder, domainfile, problemfile)
    search_strategy = config.get("search")
    # create an instance of the search strategy and dump the generated SMTLIB code
    search_strategy(encoder_instance, schedule).dump_smtlib_to_file(bound, path)