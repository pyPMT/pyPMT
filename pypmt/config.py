import os
import logging

from unified_planning.shortcuts import CompilationKind
from pypmt.encoders.R2E import EncoderRelaxed2Exists
from pypmt.encoders.basic import EncoderForall, EncoderSequential
from pypmt.encoders.SequentialLifted import EncoderSequentialLifted
from pypmt.encoders.SequentialQFUF import EncoderSequentialQFUF
from pypmt.encoders.OMT import EncoderSequentialOMT

from pypmt.planner.SMT import SMTSearch
from pypmt.planner.SMTActionPropagator import SMTSearchActionPropagator
from pypmt.planner.SMTStateAndActionPropagator import SMTSearchStateAndActionPropagator
from pypmt.planner.SMTStatePropagator import SMTSearchStatePropagator
from pypmt.planner.lifted import LiftedSearch
from pypmt.planner.QFUF import QFUFSearch
from pypmt.planner.OMT import OMTSearch
from pypmt.propagators.base import BasePropagator
from pypmt.propagators.h2propagator import H2Propagator

class Config:
    """
    A class used to manage a configuration setting for the application.

    Attributes
    ----------
    config : dict
        A dictionary storing the configuration settings with default values.
    valid_config_values : dict
        A dictionary describing the valid configuration keys and their descriptions.

    Methods
    -------
    get(key): Retrieves the value associated with the given key from the configuration.
    set(key, value) : Sets the value for the given key in the configuration if the key is valid.
    set_verbosity(value): Configures the logger to output the appropriate level of messages based on the verbosity value.
    set_config(parameters): Sets the global configuration with the provided parameters.
    """ 

    # Valid configuration keys for pyPMT and their descriptions
    valid_keys = {
        "verbose": "Controls the level of verbosity (0,4)",
        "ub": "the upper bound on the number of possible steps considered",
        "output_file": "the file where the SMTLIB encoding will be written for the dump action",
        "encoded_step": "the step that will be encoded for the dump action",
        "logger": "a logging python object that controls where messages go",

        "encoder": "The encoder class used to encode the problem",
        "search": "The search algorithm that the class will use",
        "compilationlist": "The list of compilation steps to apply to the task before encoding",
        "propagator": "If a propagator class has to be used to help during search",
    }

    # valid configs that the library is able to operate with
    grounded_encoders_default_compilation_list = [
        ('up_quantifiers_remover', CompilationKind.QUANTIFIERS_REMOVING), 
        ('up_disjunctive_conditions_remover', CompilationKind.DISJUNCTIVE_CONDITIONS_REMOVING), 
        ('up_grounder', CompilationKind.GROUNDING)
    ]
    lifted_encoders_default_compilation_list = []

    valid_configs = {
        "seq": {
            "encoder": EncoderSequential,
            "search": SMTSearch,
            "compilationlist": grounded_encoders_default_compilation_list,
            "propagator": None
        },
        "seqProp": {
            "encoder": EncoderSequential,
            "search": SMTSearchActionPropagator,
            "compilationlist": grounded_encoders_default_compilation_list,
            "propagator": BasePropagator
        },
        "seqH2Prop": {
            "encoder": EncoderSequential,
            #"search": SMTSearchStateAndActionPropagator,    
            "search": SMTSearchStatePropagator,    
            "compilationlist": grounded_encoders_default_compilation_list,
            "propagator": H2Propagator
        },
        "forall": {
            "encoder": EncoderForall,
            "search": SMTSearch,
            "compilationlist": grounded_encoders_default_compilation_list,
            "propagator": None
        },
        "r2e": {
            "encoder": EncoderRelaxed2Exists,
            "search": SMTSearch,
            "compilationlist": grounded_encoders_default_compilation_list,
            "propagator": None
        },
        "uf": {
            "encoder": EncoderSequentialLifted,
            "search": LiftedSearch,
            "compilationlist": lifted_encoders_default_compilation_list,
            "propagator": None
        },
        "qfuf": {
            "encoder": EncoderSequentialQFUF,
            "search": QFUFSearch,
            "compilationlist": lifted_encoders_default_compilation_list,
            "propagator": None
        },
        "omtseq": {
            "encoder": EncoderSequentialOMT,
            "search": OMTSearch,
            "compilationlist": grounded_encoders_default_compilation_list,
            "propagator": None
        }
    }

    valid_configs_description = {
        "seq": "Use the sequential SMT encoding",
        "seqProp": "A sequential SMT encoding with the Base propagator",
        "seqH2Prop": "A sequential SMT encoding with the H2 propagator",
        "forall": "Use the parallel SMT encoding with forall-step semantics",
        "r2e": "Use the R2E encoding",
        "uf": "Use the lifted encoding with quantifiers",
        "qfuf": "Use the quantifier-free lifted encoding",
        "omtseq": "Use the sequential OMT encoding"
    }

    def __init__(self, initial_config=None):
        # We initialise it with default values
        logging.basicConfig(format='%(asctime)s %(message)s')
        self.config = {
            # dump
            "output_file": None,
            "encoded_step": None,

            # solve
            "ub": 100,

            # common
            "verbose": 1,
            "logger": logging.getLogger(__name__),
            "encoder": None,
            "search": None,
            "compilationlist": None,
            "propagator": None,
        }
        # and copy over any non-default values
        if initial_config:
            self.set_config(initial_config)

    def get(self, key):
        return self.config[key]

    def set(self, key, value):
        """ Set a value in the config """
        if key in self.valid_keys.keys():
            if key == "verbose":
                self.set_verbosity(value)
            elif key == "output_file":
                self.set_output_file(value)
            else:
                self.config[key] = value
        else:
            raise ValueError(f"Trying to set config {key}={value} but key {key} is not known")

    def set_output_file(self, path):
        """ Set the output file for the encoding. Checks that the given path is writable """
        # Extract the directory path from the full path
        full_path = os.path.abspath(path) # if relative, transform to absolute
        directory = os.path.dirname(full_path)

        # Check if the file can be created at the specified path
        if os.access(directory, os.F_OK) and os.access(directory, os.W_OK):
            self.config["output_file"] = full_path
        else:
            raise ValueError(f"Cannot write to the specified output file path: {full_path}")

    def set_verbosity(self, value):
        """ 
        Configures the logger to output the right amount of messages 
        Roughly, the idea is to have:
        0: nothing. Useful when used as a library I guess
        1: basic informative messages and solutions printed 
        2: add timing information 
        3: add both z3 and general stats
        4: step by step traces on what the code is doing
        """
        logger = self.config["logger"]
        assert(logger is not None)
        if value == 0:
            level = logging.CRITICAL
        elif value == 1:
            level = logging.ERROR
        elif value == 2:
            level = logging.WARNING
        elif value == 3:
            level = logging.INFO
        elif value >= 4:
            level = logging.DEBUG
        else:
            raise ValueError(f"Invalid verbosity level: {value}")

        logger.setLevel(level)
        for handler in logger.handlers:
            handler.setLevel(level)

    def set_config(self, param):
        """
        Set the global config with the parameters given.
        param (dict, str, or Config): A dictionary containing the configuration keys and their corresponding values to be set,
                                     a string representing a key in the valid_configs dictionary,
                                     or a Config object to replace the current configuration.
        Raises a ValueError if any key in the parameters dictionary is not a valid configuration key.
        """
        if isinstance(param, dict):
            config_values = param

        elif isinstance(param, str):
            config_values = self.valid_configs.get(param)
            if config_values is None:
                raise ValueError(f"Invalid configuration key: {param}")

        elif isinstance(param, Config):
            self.config = param.config.copy()
            return
        else:
            raise TypeError("Parameters must be either a dictionary, a string, or a Config object.")

        for key, value in config_values.items():
            self.set(key, value)

    def get_valid_configs(self):
        """
        Retrieve a dictionary of valid configurations and their descriptions.

        This method constructs a dictionary where the keys are the valid configuration
        names and the values are their corresponding descriptions.
        Used to automatically generate the help message for the command line interface.

        Returns:
            dict: A dictionary with configuration names as keys and their descriptions as values.
        """
        return {key: self.valid_configs_description[key] for key in self.valid_configs}

# the global configuration. It is set from the apis.py file
global_config = Config()