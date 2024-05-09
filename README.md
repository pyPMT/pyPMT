# pyPMT
A Python library for Planning Modulo Theories using SMT

## Installing pyPMT

Install the package using `pip`:
```
python -m pip install .
```

## Using pyPMT

##### Getting help

To see the list of input arguments, type

```
pypmtcli -h
```

##### Running pyPMT

To run pyPMT on a problem from the CLI, type, e.g.,
```
pypmtcli --seq --bound 3 --domain path_to_domain.pddl --problem path_to_problem.pddl
```

To produce an SMT-LIB encoding of the problem (instead of solving it), type, e.g.

```
pypmtcli --seq --bound 3 --domain path_to_domain.pddl --problem path_to_problem.pddl --dump
```

pyPMT can be used as a library too. See [here](https://github.com/pyPMT/quick-start) for some examples.

## Documentation

Further documentation is available [here]().


## Authors

[Mustafa F Abdelwahed](https://github.com/MFaisalZaki)
[Joan Espasa Arxer](https://github.com/JoanEspasa)
[Francesco Leofante](https://fraleo.github.io)

Do not hesitate to contact us if you have problems using pyPMT, or if you find bugs :)