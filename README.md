# pyPMT: A Python Library for Planning Modulo Theories using SMT

## Installation

Install pyPMT using `pip`:

```sh
python -m pip install .
```

## Usage

### Getting Help

To see the list of input arguments, type:

```sh
pypmtcli -h
```

### Running pyPMT

To run pyPMT on a problem from the CLI, type, for example:

```sh
pypmtcli solve --encoding seq --domain domain.pddl --problem problem.pddl
```

To produce an SMT-LIB encoding of the problem (instead of solving it), type, for example:

```sh
pypmtcli dump --encoding seq --domain domain.pddl --problem problem.pddl --output_file foo.smt2 --step 10
```

pyPMT can also be used as a library. See [quick-start examples](https://github.com/pyPMT/quick-start) for more details.

## Documentation

Further documentation is available [here](https://github.com/pyPMT/pyPMT/blob/main/refman.pdf).

## Known Limitations

- In domains like `promela-dining-philosophers-fluents-adl` or `psr`, nested foralls in the effects are not supported 
- The `tidybot-sequential-optimal` domain exceed the maximum recursion depth of the PDDL Parser
- ID overloading is not supported. For example, a predicate and function with the same name

## Authors

- [Mustafa F Abdelwahed](https://github.com/MFaisalZaki)
- [Joan Espasa Arxer](https://joanespasa.github.io/)
- [Francesco Leofante](https://fraleo.github.io)

Feel free to contact us if you encounter any issues or find bugs.

## Contributing

We welcome contributions! Please see our [CONTRIBUTING](https://github.com/pyPMT/pyPMT/blob/main/CONTRIBUTING.md) guide for more details.