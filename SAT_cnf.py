import re
from typing import Any
import random

# Two defined values for literals (the polarity)
POS_LIT = 1 # positive literal, like x1
NEG_LIT = 0 # negative literal, like ~x1

class Clause:
    '''
    Clause Class. Reference https://www.geeksforgeeks.org/python-linked-list/
    '''
    def __init__(self, number, data: dict, isCNF=True):
        #Assign number to the clause
        self.number = number

        #Assign data to clause. Should be the CNF clause. Possibly dictionary?
        self.data: dict = data

        # Set to confirm if clause is in CNF form
        self.isCNF: bool = isCNF

        # Set to confirm if clause is SAT
        self.isSAT: bool = False

        self.isUnitClause = False

    '''
    Writes the clause in a mathematical way
    '''
    def __str__(self) -> str:
        pairs: list[tuple] = [] # pairs of: (var_i, value)
        for var_i in sorted(self.data.keys()):
            val = self.data[var_i]
            pairs.append((var_i, val))
        vars: list[str] = [f"x{i}" if v else f"~x{i}" for i, v in pairs]
        if self.isCNF:
            return "(" + " + ".join(vars) + ")"
        else:
            return " . ".join(vars)

    def __repr__(self) -> str:
        return str(self)

'''
Create a `Clause` given:
- `ones`: the list of variables (as integers) that are positive literals (e.g. x1)
- `zeros`: the list of variables (as integers) that are negative literals (e.g. ~x1)
Note: the created clause will have a `.number` of 0 because I don't know what to put there.
Example:
  createClause([1,2,4], [3,5]) represents the CNF clause "(x1 + x2 + x3' + x4 + x5')"
[Izak is responsible for this function.]
'''
def make_CNF_clause(ones: set[int]|list[int], zeros: set[int]|list[int]) -> Clause:
    return Clause(number=0, data=make_CNF_dict(ones, zeros))


'''
Helper function for make_CNF_clause
[Izak is responsible for this function.]
'''
def make_CNF_dict(ones: set[int]|list[int], zeros: set[int]|list[int]) -> dict[int,int]:
    ones = set(ones)
    zeros = set(zeros)
    if both := set.intersection(ones, zeros):
        raise ValueError(f"variables {both} should not be in both the `ones` set and the `zeros` set")
    clause = dict()
    for var_i in ones:
        clause[var_i] = 1
    for var_i in zeros:
        clause[var_i] = 0
    return clause


'''
Parses a Sum-of-Products boolean function string.
The expected string format is:
- "x"<integer> denotes a variable
- "~" for logical negation
- "+" for logical or
- "." optional for logical and, otherwise logical and is implicit
Returns: a list of `Clause`s, but they are product terms, NOT CNF clauses!
NOTE: this function parses pretty greedily and optimistically and may accept and
    parse strings that are not exactly in the right syntax, such as with double
    negatives, multiple dots, extra letters, etc.
[Izak is responsible for this function.]
'''
def parse_SOP_string(text: str) -> list[Clause]:
    if not re.match(r"^([ \r\n.~+x0-9])+$", text, flags=re.IGNORECASE):
        raise ValueError("text has forbidden characters for SOP form")
    clauses: list[Clause] = []
    # split apart all of the product terms which are OR'ed together
    terms = text.split('+')
    # pattern to match one postive or negative literal
    # - group #1 captures the optional inversion prefix '~'
    # - group #2 captures the variable subscript number (the i value in "xi")
    lit_pattern = re.compile('(~?) *x([0-9]+)', flags=re.IGNORECASE)
    for term in terms:
        # get all of the literals in this term
        literals = lit_pattern.findall(term)
        # group the literals into positive and negative
        positives = [int(i) for prefix, i in literals if not prefix]
        negatives = [int(i) for prefix, i in literals if prefix]
        clause = make_CNF_clause(positives, negatives)
        clause.isCNF = False # this flag is for debugging/error checking purposes
        clauses.append(clause)
    return clauses


'''
Convert a list of SOP clauses (like from the result of parse_SOP_string) to a list of CNF clauses.
The basic process of inverting it twice, referenced in
[https://web.archive.org/web/20171226054911/http://mathforum.org/library/drmath/view/51857.html]
is too slow when selecting the minterms (2^n).
So lets use gate consistency functions!
[Izak is responsible for this function.]
'''
def convert_SOP_to_CNF(productTerms: list[Clause]) -> list[Clause]:
    # Get the last/highest variable index value, xi
    max_var_i: int = max([max(term.data.keys()) for term in productTerms])
    extra_var_i = max_var_i + 1
    final_output_var_i = 1 + max_var_i + len(productTerms)
    CNF: list[Clause] = []
    # Add the CNF clauses from the AND terms from the SOP form
    for i, term in enumerate(productTerms):
        if term.isCNF:
            raise ValueError(f"the term \"{term}\" should not be marked as isCNF")
        and_output_var = extra_var_i + i
        add_and_GCF(CNF, term.data, and_output_var)
    # Add the CNF clauses from the single OR gate consistency function.
    # The inputs to the OR are all of the AND output variables.
    or_input_vars = range(extra_var_i, extra_var_i + len(productTerms))
    add_or_GCF(CNF, or_input_vars, final_output_var_i)
    # Add the final clause: the fact that the output variable should be 1
    CNF.append(make_CNF_clause(ones=[final_output_var_i], zeros=[]))
    return CNF


'''
Helper function for convert_SOP_to_CNF()
GCF stands for Gate Consistency Function.
Given a product term (from SOP form), and it's output variable,
add all of it's required CNF clauses to the `toList` as determined by the AND gate consistency function (GCF).
[Izak is responsible for this function.]
'''
def add_and_GCF(toList: list[Clause], term: dict[int, Any], term_out_var_i: int):
    # Each term is a product (AND gate)
    # and the consistency function for this creates multiple CNF clauses:
    # For a single gate z = AND(x1, x2, ... xn):
    #     [PRODUCT(over i=1 to n, of (xi + ~z))] * [SUM(over i=1 to n, of ~xi) + z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    [PRODUCT(over i=1 to n, of xi + ~z)]
    for x_i, val in term.items():
        pos = []
        neg = [term_out_var_i] # add ~z
        if val == 1:
            # `var_i` is a positive literal in the product term
            pos.append(x_i) # add xi
        elif val == 0:
            # `var_i` is a negative literal in the product term
            neg.append(x_i) # add xi
        else:
            raise ValueError(f"term variable #{x_i} has invalid value: {val}")
        toList.append(make_CNF_clause(ones=pos, zeros=neg))

    # Add a single CNF clause for the SUMATION part:
    #    [SUM(over i=1 to n, of ~xi) + z]
    pos = [x_i for x_i, val in term.items() if val == 0] # add ~xi (invert the var's polarity)
    neg = [x_i for x_i, val in term.items() if val == 1] # add ~xi (invert the var's polarity)
    pos.append(term_out_var_i) # add z
    toList.append(make_CNF_clause(ones=pos, zeros=neg))



'''
Helper function for convert_SOP_to_CNF().
GCF stands for Gate Consistency Function.
Create the consistency function for the OR gate that occurs in SOP form.
All the input variables are positive, which is why this function is simpler than `add_and_GCF()`.
[Izak is responsible for this function.]
'''
def add_or_GCF(toList: list[Clause], or_input_vars, output_var: int):
    # For and OR gate z = OR(x1, x2, ... xn):
    #    [PRODUCT(over i=1 to n, of (~xi + z))] * [SUM(over i=1 to n, of xi) + ~z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    PRODUCT(over i=1 to n, of (~xi + z))
    for x_i in or_input_vars:
        toList.append(make_CNF_clause(ones=[output_var], zeros=[x_i]))

    # Add a single CNF clause for the SUMATION part:
    #    [SUM(over i=1 to n, of xi) + ~z]
    # In this part, we invert each literals' polarity between positive/negative
    toList.append(make_CNF_clause(ones=list(or_input_vars), zeros=[output_var]))


# placeholder functions::
# These could both be replaced by a single function that returns different values that represent the clause's state
def clause_is_UNSAT(clause: Clause, decisions: dict):
    '''
    Function to return if clause is UNSAT.
    Return True if function is UNSAT
    Return False if function is SAT
    '''
    list_of_literals = list(clause.data)
    decision_literals = list(decisions.keys())
    num_of_literals = len(list_of_literals)
    count = 0
    for i in range(len(list_of_literals)):
        current_literal = list_of_literals[i]
        for j in range(len(decision_literals)):
            if current_literal == decision_literals[j]:
                if decisions[decision_literals[j]] == NEG_LIT:
                    count += 1
    if count == num_of_literals:
        return True
    return False
            
    
def clause_is_undecided(clause, decisions): pass


def decide_literal(clauses: list[Clause], decisions: dict) -> int:
    '''
    Choose an unassigned literal to try next.
    '''
    undecided = [xi for xi, value in decisions.items() if value is None]
    # For now, just choose a random undecided variable.
    return random.choice(undecided)


def all_undecided(clauses:list[Clause]) -> dict[int,Any]:
    # Initialize the assignments dictionary to have all variables undecided.
    assignments: dict[int, Any] = dict()
    max_var_i = max([max(clause.data.keys()) for clause in clauses])
    for i in range(1, max_var_i + 1):
        assignments[i] = None
    return assignments


def dpll(clauses:list[Clause]) -> dict[int,Any]|str:
    '''
    DPLL algorithm for SAT solving.
    Takes in a list of CNF clauses and a dictionary of decisions (which may be initially empty).
    Returns the decisions for literals that make the SAT problem true,
    or 'UNSAT' if no decisions can make the function SAT.
    '''
    return dpll_rec(clauses, assignments=all_undecided(clauses))


def dpll_rec(clauses:list[Clause], assignments:dict) -> dict[int,Any]|str:
    '''
    Helper function for dpll.
    '''
    # Base cases:
    # - if all clauses are SAT, then return the assignments.
    # - if any clause is UNSAT, then return 'UNSAT'.
    anyUndecided = False
    for clause in clauses:
        # If any clause is UNSAT, then the whole function is UNSAT.
        if clause_is_UNSAT(clause, assignments):
            return 'UNSAT'
        # We only need to check if one clause is undecided to know if any are undecided.
        if not anyUndecided:
            # We haven't found any undecided clauses yet.
            if clause_is_undecided(clause, assignments):
                anyUndecided = True
    if not anyUndecided:
        # All clauses are SAT. So the whole function is SAT!
        return assignments

    # At this point, the clauses are undecided.
    # Choose a literal to try to assign to 1 or to 0...
    # And try those options out by branching recursively.
    xi = decide_literal(clauses, assignments)
    # Try xi=1
    assignments[xi] = 1
    if (result := dpll_rec(clauses, assignments)) != 'UNSAT':
        return result
    # Try xi=0
    assignments[xi] = 0
    if (result := dpll_rec(clauses, assignments)) != 'UNSAT':
        return result
    # If both xi=1 and xi=0 failed, then this whole recursive branch is UNSAT.
    # So return UNSAT to the callee (probably the previous recursive call).
    assignments[xi] = None # undo the decision
    return 'UNSAT'


def printAssignments(assignments: dict[int,Any]):
    print("\n".join([f"x{i}={v}" for i, v in assignments.items()]))


sop_str = "x1.x3 + ~x1.x2"
print('Parsing SOP input:', sop_str)
sop = parse_SOP_string(sop_str)
print('Parsed result:', str(sop))
print('Converting to CNF, clauses are:')
cnf = convert_SOP_to_CNF(sop)
print(".".join([str(c) for c in cnf])) # print clause list
n = max(cnf[-1].data.keys()) # quick and overly specific way to do this
print(f"The output variable is x{n} and must be set to 1.")

result = dpll(cnf)
if type(result) == dict:
    print("Function is SAT with these assignments:")
    printAssignments(result)
else:
    print("Function is UNSAT")