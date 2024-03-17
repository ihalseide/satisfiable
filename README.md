# satisfiable

A simple SAT solver (boolean function satisfiability).

# Running

```
python3 SAT_cnf.py ...args...
```

Arguments:

```
usage: SAT_cnf.py [-h] [-f FILE] [-x] [-a | -o] [-p] [-d DIMACS] [-m | -s]

Provide path to file with boolean function to check for SAT or UNSAT. File must contain at least one function and no more than two.
Functions MUST be in SoP form. If two functions are in file, pass in [-x, --xor] flag to find SAT on two functions.

options:
  -h, --help            show this help message and exit
  -a, --all-sop         Find all solutions for function in SoP form
  -o, --one-sop         Find one solution for function in SoP form
  -m, --all-dimacs      Find all solutions for function in DIMACS form
  -s, --one-dimacs      Find one solution for function in DIMACS form

  -f FILE, --file FILE  SoP file to parse function in SoP form
  -x, --xor             XOR two SoP functions and return SAT or UNSAT
  -p, --print           Print the DIMACS form of a SoP function from a file. Only use with [-f, --file] option

  -d DIMACS, --dimacs DIMACS
                        DIMACS file to parse instead of a function in SoP form
```