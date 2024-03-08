import re
from typing import Any
import random


# Two defined values for literals (the polarity)
POS_LIT = 1 # positive literal, like x1
NEG_LIT = 0 # negative literal, like ~x1


class Clause:
    '''
    Clause class, which represents a clause in (CNF) Conjunctive Normal Form.
    '''
    def __init__(self, number, data: dict[int, Any]):
        #Assign number to the clause
        self.number = number
 
        # Assign data to clause. Should be the CNF clause
        # Maps variable index -> value.
        # For example, a variable index of `1` means the boolean function input variable "x1"
        self.data: dict[int,Any] = data

    def sortedVars(self):
        '''
        Get all of the variable indices and values, sorted by increasing variable index.
        Example: [(1,0),(2,0),(3,1)] is the output for a clause like "(x3 + ~x1 + ~x2)"
        '''
        return sorted(self.data.items())

    def __str__(self, isCNF:bool=True) -> str:
        '''
        Get a readable string version of this clause.
        This method gets called automatically by str().
        '''
        vars: list[str] = [f"x{i}" if (v == 1) else f"~x{i}" for i, v in self.sortedVars()]
        sep: str = " + " if isCNF else " . "
        return f"({sep.join(vars)})"

    def __repr__(self) -> str:
        '''
        String representation for a clause, just use the same readable version.
        This method is called automatically by repr() and str().
        '''
        return str(self)


def make_CNF_clause(ones: set[int]|list[int], zeros: set[int]|list[int], number=0) -> Clause:
    '''
    Create a Clause given:
    - `ones`: the list/set of variables (as ints) that are POSITIVE literals (e.g. x1)
    - `zeros`: the list/set of variables (as ints) that are NEGATIVE literals (e.g. ~x1)
    - `number`: optional clause number/id

    Examples:
    - createClause([1,2,4], [3,5]) represents the CNF clause: "(x1 + x2 + ~x3 + x4 + ~x5)"
    - createClause([3,2], []) represents the CNF clause: "(x3 + x2)"
    - createClause([], [6]) represents the CNF clause: "(~x6)"
    - createClause([], []) represents an (empty) CNF clause: "()"

    [Izak is responsible for this function.]
    '''
    return Clause(number=number, data=make_CNF_dict(ones, zeros))


def make_CNF_dict(ones: set[int]|list[int], zeros: set[int]|list[int]) -> dict[int, int]:
    '''
    Create the data dictionary that maps literal indices to values (postive/negative literal)
    (Helper function for make_CNF_clause).
    - `ones`: the list/set of variables (as ints) that are POSITIVE literals (e.g. x1)
    - `zeros`: the list/set of variables (as ints) that are NEGATIVE literals (e.g. ~x1)
    Returns: dictionary, where keys are the literal indices,
       and where values mark the literal's polarity (positive/negative).
    [Izak is responsible for this function.]
    '''
    ones = set(ones)
    zeros = set(zeros)
    if in_both := set.intersection(ones, zeros):
        # NOTE: This might not be an error if this function is ever used to create new clauses in the actual SAT-solver algorithm.
        raise ValueError(f"variables {in_both} should not appear as a positive literal and a negative literal")
    d = dict()
    for var_i in ones:
        d[var_i] = POS_LIT
    for var_i in zeros:
        d[var_i] = NEG_LIT
    return d


def parse_SOP_string(text: str) -> list[Clause]: # not CNF clauses!
    '''
    Parses a Sum-of-Products boolean function string.

    The expected string format is:
    - "x"<integer> denotes a variable
    - "~" for logical negation
    - "+" for logical or
    - "." optional for logical and, otherwise logical and is implicit

    Return value: a list of `Clause`s, BUT they are NOT CNF clauses!!!
        They are product terms (DNF clauses).

    NOTE: this function parses pretty greedily and optimistically and may accept and
        parse strings that are not exactly in the right syntax, such as with double
        negatives, multiple dots, extra letters, etc.

    [Izak is responsible for this function.]
    '''
    # Make sure only this subset of characters is in the input string
    if not re.match(r"^([ \r\n.~+x0-9])+$", text, flags=re.IGNORECASE):
        raise ValueError("text string has forbidden characters for SOP form")
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
        clauses.append(clause)
    return clauses


def convert_SOP_to_CNF(productTerms: list[Clause]) -> list[Clause]:
    '''
    Convert a list of SOP clauses (like from the result of parse_SOP_string) to a list of CNF clauses.

    Conversion technique: Gate Consistency Functions (GCF).

    Return value: a list of CNF clauses.

    NOTE: the highest literal/variable index in the CNF clauses is the output variable.

    [Izak is responsible for this function.]
    '''
    # Get the last/highest variable index value, xi:
    max_var_i: int = find_maximum_literal(productTerms)
    # Use this as the first new variable index that can be introduced:
    extra_var_i = max_var_i + 1
    # Literal index for the function's final output wire/literal
    # (Each product term introduces one new literal, its output wire).
    final_output_var_i = 1 + max_var_i + len(productTerms)
    CNF: list[Clause] = []
    # Add the CNF clauses from the AND terms from the SOP form
    for i, term in enumerate(productTerms):
        and_output_var = extra_var_i + i
        add_and_GCF(CNF, term.data, and_output_var)
    # Add the CNF clauses from the single OR gate consistency function.
    # The inputs to the OR are all of the AND output variables.
    or_input_vars = range(extra_var_i, extra_var_i + len(productTerms))
    add_or_GCF(CNF, or_input_vars, final_output_var_i)
    # Add the final clause: the fact that the output variable should be 1/true
    CNF.append(make_CNF_clause(ones=[final_output_var_i], zeros=[]))
    return CNF


def add_and_GCF(toList: list[Clause], term: dict[int, Any], term_out_var_i: int):
    '''
    Helper function for convert_SOP_to_CNF().
    (GCF stands for Gate Consistency Function.)

    Given a product term (from SOP form), and it's output variable,
    add all of it's required CNF clauses to the `toList` as determined by the AND gate consistency function (GCF).

    [Izak is responsible for this function.]
    '''
    # Each term is a product (AND gate)
    # and the consistency function for this creates multiple CNF clauses:
    # For a single gate z = AND(x1, x2, ... xn):
    #     [PRODUCT(over i=1 to n, of (xi + ~z))] * [SUM(over i=1 to n, of ~xi) + z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    [PRODUCT(over i=1 to n, of xi + ~z)]
    for x_i, val in term.items():
        pos = []
        neg = [term_out_var_i] # add ~z
        if val == POS_LIT:
            # `var_i` is a positive literal in the product term
            pos.append(x_i) # add xi
        elif val == NEG_LIT:
            # `var_i` is a negative literal in the product term
            neg.append(x_i) # add xi
        else:
            raise ValueError(f"term variable #{x_i} has invalid value: {val}")
        toList.append(make_CNF_clause(ones=pos, zeros=neg))

    # Add a single CNF clause for the SUMATION part:
    #    [SUM(over i=1 to n, of ~xi) + z]
    pos = [x_i for x_i, val in term.items() if val == NEG_LIT] # add ~xi (invert the var's polarity)
    neg = [x_i for x_i, val in term.items() if val == POS_LIT] # add ~xi (invert the var's polarity)
    pos.append(term_out_var_i) # add z
    toList.append(make_CNF_clause(ones=pos, zeros=neg))


def add_or_GCF(toList: list[Clause], or_input_vars, output_var: int):
    '''
    Helper function for convert_SOP_to_CNF().
    (GCF stands for Gate Consistency Function.)

    Create the consistency function for the OR gate that occurs in SOP form.
    All the input variables are positive, which is why this function is simpler than `add_and_GCF()`.

    [Izak is responsible for this function.]
    '''
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


# placeholder function:
def clause_value_given_assignments(clause, assignments): pass


def find_maximum_literal(clauses: list[Clause]) -> int:
    '''
    Find the maximum variable index in a list of CNF clauses.
    This is useful for knowing the upper limit of how many variables there are in a boolean function.
    Also useful for finding the output variable index.
    '''
    return max([max(clause.data.keys()) for clause in clauses])


def decide_literal(clauses: list[Clause], decisions: dict) -> int:
    '''
    Choose an unassigned literal to try next.
    '''
    undecided = [xi for xi, value in decisions.items() if value is None]
    # For now, just choose a random undecided variable.
    return random.choice(undecided)


def all_undecided(clauses:list[Clause]) -> dict[int,Any]:
    '''
    Helper function for dpll() to create initial assignments where each variable is undecided.
    (So each xi is set to None.)
    '''
    # Initialize the assignments dictionary to have all variables undecided.
    assignments: dict[int, Any] = dict()
    max_var_i = find_maximum_literal(clauses)
    for i in range(1, max_var_i + 1):
        assignments[i] = None
    return assignments


def dpll(clauses:list[Clause]) -> dict[int,Any]:
    '''
    DPLL algorithm for SAT solving.
    Takes in a list of CNF clauses representing a boolean function.
    Returns: the assignments for literals that make the SAT problem true, or returns 'UNSAT' if no decisions can make the function SAT.
    '''
    # Start out with all variables undecided.
    assignments = all_undecided(clauses)
    # But, assign the output literal/variable to be 1
    output_var_i = find_maximum_literal(clauses)
    assignments[output_var_i ] = 1
    return dpll_rec(clauses, assignments)


def dpll_rec(clauses:list[Clause], assignments:dict) -> dict[int,Any]:
    '''
    The recursive function implementation for dpll().
    Takes in a list of CNF clauses and a dictionary of decisions.
    Returns: the assignments for literals that make the SAT problem true,
    which is an empty dictionary if the function is UNSAT.
    '''
    # Base cases:
    # - if all clauses are SAT, then return the assignments.
    # - if any clause is UNSAT, then return 'UNSAT'.
    anyUndecidedClause: bool = False
    for clause in clauses:
        value = clause_value_given_assignments(clause, assignments)
        if value == 'UNSAT':
            # If any clause is UNSAT, then the whole function is UNSAT.
            return {} # UNSAT
        elif value == 'UNDECIDED':
            # We only need to see that one clause is undecided to know if any are undecided.
            anyUndecidedClause = True
    if not anyUndecidedClause:
        # If no clauses are UNSAT and no clauses are undecided,
        # then all clauses are SAT and the whole function is SAT!
        return assignments # SAT

    # At this point, the clauses are undecided.
    # Choose a literal to try to assign to 1 or to 0...
    # And try those options out by branching recursively.
    xi: int = decide_literal(clauses, assignments)
    assert(assignments[xi] is None)
    # Try xi=1
    assignments[xi] = 1
    if (result := dpll_rec(clauses, assignments)):
        # SAT
        return result
    # Try xi=0
    assignments[xi] = 0
    if (result := dpll_rec(clauses, assignments)):
        # SAT
        return result
    # If both xi=1 and xi=0 failed, then this whole recursive branch is UNSAT.
    # So return UNSAT to the callee (probably the previous recursive call).
    assignments[xi] = None # undo the decision
    return {} # UNSAT


def make_blocking_clause(assignments: dict[int,Any]) -> Clause:
    '''
    Create a clause that blocks the solution given by the assignments.
    Just have to negate the current decided assignments.
    '''
    pos = [xi for xi, v in assignments.items() if v == NEG_LIT] # negated
    neg = [xi for xi, v in assignments.items() if v == POS_LIT] # negated
    return make_CNF_clause(pos, neg)


def find_all_SAT(clauses: list[Clause]) -> list[dict[int,Any]]:
    '''
    Find all satisfying assignments for a boolean function in CNF.
    '''
    solutions: list[dict[int,Any]] = []
    while (result := dpll(clauses)):
        # Add the current solution to the list of solutions
        solutions.append(result)
        # Add a new clause to the CNF that blocks the current solution
        # (i.e. add a clause that makes the current solution UNSAT).
        # This is called "blocking" the solution.
        clauses.append(make_blocking_clause(result))
    return solutions


def boolean_functions_are_equivalent(clauses1: list[Clause], clauses2: list[Clause]) -> bool:
    '''
    Check if two sets of CNF clauses represent the same boolean function by using SAT solving.
    Does this by XOR'ing the two sets of clauses and checking if the result is UNSAT.
    '''
    # XOR the two sets of clauses together,
    # Using gate consistency functions for AND and OR to implement (a^b) as (~a.b + a.~b).
    assert(False) # not implemented yet


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
if result:
    print("Function is SAT with these assignments:")
    printAssignments(result)
else:
    print("Function is UNSAT")
