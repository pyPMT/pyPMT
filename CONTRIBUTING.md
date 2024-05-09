# Contributing to the project

First off, thanks for taking the time to consider contributing.
If you have found a bug, please report all the necessary information to reproduce it and describe the issue in detail. 

## Adding a new encoding

To integrate a new encoding there are a few requirements:
- Create a new file in `encoders` and inherit from `Encoder` in `base.py`.
- Overwrite the `__iter__` and `__len__` methods to respectively go through the actions and give the maximum bound of the encoded formula
- The basic search method in `planner/SMT.py` (the `SMTSearch` class) needs the encoder to have the `encode(t)` method, a `ctx` attribute to be able to assert the bound and the `extract_plan` method. 
- in `shared/valid_configs.py` you can add the new configuration for the encoding.
- in `omtplancli.py` you can add support for it in the CLI interface. This should at some point be automated from the configurations though ...

## Adding a new search procedure

Sometimes a new encoding will require a specialised search procedure. Other search strategies might be interesting to explore and beneficial in certain scenarios. To easily integrate a new search method:

- Create a new file in `planner/` and inherit from the `planner/base.py`.
- Implement the `search` method, which returns a plan.
- In `shared/valid_configs.py` you can add match it with which encodings are valid.


