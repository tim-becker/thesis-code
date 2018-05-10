Representations and Complexity of Abelian Automaton Groups
==========================================================

This repository implements code used in my senior thesis. Note that it will be
updated fairly frequently.

See [binary\_invertible\_transducer.sage](./binary_invertible_transducer.sage)
for
* An implementation of binary invertible transducers
* Computation and estimation of their groups
* Computation of group representations for abelian transducers

See [abelian\_conjectures.sage](./abelian_conjectures.sage) for current
conjectures which are being tested.

## Usage
From the repo base directory, open a `sage` session. Then load in the provided
code:
```
$ sage
┌────────────────────────────────────────────────────────────────────┐
│ SageMath version 8.1, Release Date: 2017-12-07                     │
│ Type "notebook()" for the browser-based notebook interface.        │
│ Type "help()" for help.                                            │
└────────────────────────────────────────────────────────────────────┘
sage: load('./binary_invertible_transducer.sage')
```

From here, all functions / classes should be loaded and ready to use.
For example,
```
sage: T = CCC(3,2)
sage: T.plot() # opens a diagram of the machine
sage: T.field_representation()

(Number Field in Z with defining polynomial z^2 + z + 1/2,
 {x0: -6/5*Z - 2/5, x1: 4/5*Z + 8/5, x2: 4/5*Z - 2/5})
```

Alternatively, you could write a script which imports the code.
For instance, if `script.sage` contains the following code,
```
load('./binary_invertible_transducer.sage')

T = CCC(3,2)
print T.field_representation()
```
then running `sage script.sage` will invoke your script.
