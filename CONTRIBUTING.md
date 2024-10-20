# Contributing to the project
First off, thanks for taking the time to consider contributing. If you have found a bug, please report all the necessary information to reproduce it and describe the issue in detail. You can do this by creating a new issue on our [GitHub Issues page](https://github.com/pyPMT/pyPMT/issues).

## Adding a new encoding

The `Encoder` encapsulates all the knowledge of the mapping between the UP problem class and the Z3 encoding. This means that the `Encoder` is responsible for translating the problem domain into a format that the Z3 solver can understand and work with.

To integrate a new encoding there are a few requirements:
- Create a new file in `encoders` and inherit from `Encoder` in `base.py`.
- Overwrite the `__iter__` and `__len__` methods to respectively go through the actions and give the maximum bound of the encoded formula.
- The basic search method in `planner/SMT.py` (the `SMTSearch` class) needs the encoder to have the `encode(t)` method, a `ctx` attribute to be able to assert the bound and the `extract_plan` method.
- In `config.py` you can the new encoding in a new configuration.

## Adding a new search procedure

Sometimes a new encoding will require a specialised search procedure. Other search strategies might be interesting to explore and beneficial in certain scenarios. To easily integrate a new search method:

- Create a new file in `planner/` and inherit from the `planner/base.py`.
- Implement the `search` method, which returns a plan.
- In `config.py` you can match it with which encodings are valid.

## Adding a new config

To add a new configuration in `config.py`, you need to update two dicts:

- `valid_configs`: Add the desired encoder, search procedure, etc.
- `valid_configs_description`: Provide a textual description for the CLI help.