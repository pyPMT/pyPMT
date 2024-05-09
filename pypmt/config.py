import logging

class config:
    # where the config is stored. We initialise it with default values
    logging.basicConfig(format='%(asctime)s %(message)s')
    config = {
        "verbose" : 1,
        "ub" : 100,
        "logger" : logging.getLogger(__name__),

        "encoder" : None,
        "search" : None,
        "propagator" : None,
        "extractor" : None, # Not used for now
        "validator" : None # Not used for now
    }

    valid_config_values = {
        "verbose" : "Controls the level of verbosity (0,4)",
        "ub" : "the upper bound on the number of possible steps considered",
        "logger" : "a logging python object that controls where messages go",

        "encoder" : "The encoder class used to encode the problem",
        "search" : "The search algorithm that the class will use",
        "propagator" : "If a propagator class has to be used to help during search",
        "extractor" : "The way of extracting the plan from a model",
        "validator" : "The method to validate the plan"
    }

    def get(key):
        return config.config[key]

    def set(key, value):
        """ Set a value in the config """
        if key in config.valid_config_values.keys():
            if key == "verbose":
                config.set_verbosity(value)
            else:
                config.config[key] = value
        else:
            raise ValueError(f"Trying to set config {key}={value} but key {key} is not known")

    def set_verbosity(value):
        """ 
        Configures the logger to output the right amount of messages 
        Roughly, the idea is to have:
        0: nothing. Useful when used as a library I guess
        1: basic informative messages and solutions printed 
        2: add timing information 
        3: add both z3 and general stats
        4: step by step traces on what the code is doing
        """
        logger = config.config["logger"] 
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

        logger.setLevel(level)
        for handler in logger.handlers:
            handler.setLevel(level)

    def set_config(parameters):
        """ Set the global config with the parameters given """
        raise NotImplementedError