import re
from typing import Any
import random
import argparse


# Two defined values for literals (the polarity)
POS_LIT = 1 # positive literal, like x1
NEG_LIT = 0 # negative literal, like ~x1

# Clause/function result values
SAT = 'SAT'
UNSAT = 'UNSAT'
UNDECIDED = 'UNDECIDED'


parser = argparse.ArgumentParser(description='Provide path to file with boolean function to check for SAT or UNSAT.\nFile must contain at least one function and no more than two.\nFunctions MUST be in SoP form.\nIf two functions are in file, pass in [-x, --xor] flag to find SAT on two functions.')
parser.add_argument('-f', '--file', type=str, help='Enter the abolute path to a file', required=True)
parser.add_argument('-x', '--xor', help='XOR two functions and return SAT or UNSAT', required=False, action='store_true')

args = parser.parse_args()


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
        # get list of variable names, where negated variables are prefixed with '~'
        vars: list[str] = [f"x{i}" if (v == 1) else f"~x{i}" for i, v in self.sortedVars()]
        # join the variable names together with '+' or '.'
        sep: str = " + " if isCNF else " . "
        return f"({sep.join(vars)})"

    def __repr__(self) -> str:
        '''
        String representation for a clause, just use the same readable version.
        This method is called automatically by repr() and str().
        '''
        return self.__str__()


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


def clause_value(clause: Clause, assignments: dict) -> str:
    '''
    Function to determine if clause is UNSAT or UNDECIDED.
    A clause is SAT if at least ONE literal evaluates to True
    A clause is UNSAT if all literals evaluate to False
    A clause is UNDECIDED if at least ONE literal is unassigned (This includes Unit Clauses)
    
    Return SAT if clause is SAT
    Return UNSAT if clause is UNSAT
    Return UNDECIDED if clause is UNDECIDED
    '''
    # Get the list of literals from the given clause
    list_of_literals = list(clause.data.keys())

    # Keep track of number of literals that evaluate to False
    countFalse = 0

    # Loop through the lists and compare the literal in the clause
    # with it's corresponding dictionary value
    # Returns a dictionary of the literal and it's value within the clause
    literals_and_assignments: dict = values_of_literals(clause, assignments)

    # Count number of 0's assigned in the clause
    # A clause is UNSAT if all literals are false.
    for val in literals_and_assignments.values():

        # Count the amount of 0's in a given clause
        if val == NEG_LIT:
            countFalse += 1
        
        # Return 'SAT' if any literal is 1. This means the clause is SAT
        elif val == POS_LIT:
            return SAT

    # If the amount of 0's counted in the given clause is equal to the number of
    # literals in the given clause then we know that all literals are 0.
    # This means the clause evaluates to False and is UNSAT.
    if countFalse == len(list_of_literals):
        return UNSAT
    
    # If were here then clause must be UNDECIDED since no other condition is met
    return UNDECIDED


def find_maximum_literal(clauses: list[Clause]) -> int:
    '''
    Find the maximum variable index in a list of CNF clauses.
    This is useful for knowing the upper limit of how many variables there are in a boolean function.
    Also useful for finding the output variable index.
    '''
    return max([max(clause.data.keys()) for clause in clauses])


def decide_literal(clauses: list[Clause], decisions: dict) -> int|None:
    '''
    Choose an unassigned literal to try next.
    Returns the index of the literal to try next, or None if there are no undecided literals.
    '''
    undecided = [xi for xi, value in decisions.items() if value is None]
    if not undecided:
        return None
    # For now, just choose a random undecided variable.
    return random.choice(undecided)


def values_of_literals(clause: Clause, assignments: dict) -> dict:
    '''
    Helper function to assign and get literal values of the current clause

    Return a dictionary of literal and value pairs
    '''
    # Dictionary to hold the mapping of the literal to it's value
    literal_and_assignment = dict()

    # Loop through the literals to assign the values of the literal appropriately
    # Set the current_literal to the current index of the literal
    for current_literal, val in clause.data.items():

        # If the literal is negative AND it's assigned as a 1,
        # Assign the complement 0
        if val == NEG_LIT and assignments[current_literal] == POS_LIT:
            literal_and_assignment[current_literal] = NEG_LIT

        # If the literal is negative AND it's assigned as a 0,
        # Assign the complement 1
        elif val == NEG_LIT and assignments[current_literal] == NEG_LIT:
            literal_and_assignment[current_literal] = POS_LIT
    
        # If the literal is positive, keep the current assignment
        else:
            literal_and_assignment[current_literal] = assignments[current_literal]

    # Return literal assignments
    return literal_and_assignment


def all_undecided(clauses:list[Clause]) -> dict[int,Any]:
    '''
    Helper function for dpll() to create initial assignments where each variable is undecided.
    (So each xi is set to None.)
    '''
    assignments: dict[int, Any] = dict()
    if not clauses:
        # Special case for no clauses
        return assignments
    # Initialize the assignments dictionary to have all variables undecided.
    max_var_i = find_maximum_literal(clauses)
    for i in range(1, max_var_i + 1):
        assignments[i] = None
    return assignments


# TODO: make a version of this function that uses a loop & stack instead of recursion!
def dpll(clauses:list[Clause], assignments:dict[int,Any]|None=None) -> dict[int,Any]:
    return dpll_with_stack(clauses)


def dpll_rec(clauses: list[Clause], assignments: dict[int,Any]|None=None) -> dict[int,Any]:
    '''
    The recursive function implementation for dpll().
    Takes in a list of CNF clauses and a dictionary of decisions.
    Returns: the assignments for literals that make the SAT problem true,
    which is an empty dictionary if the function is UNSAT.
    '''
    if not assignments:
        assignments = all_undecided(clauses)
    # Base cases:
    # - if all clauses are SAT, then then the function is SAT.
    # - if any clause is UNSAT, then the function is UNSAT.
    # - if there are no clauses, then the function is SAT.
    if not clauses:
        return assignments # SAT
    anyUndecidedClause: bool = False
    for clause in clauses:
        value = clause_value(clause, assignments)
        if value == UNSAT:
            # If any clause is UNSAT, then the whole function is UNSAT.
            return {} # UNSAT
        elif value == UNDECIDED:
            # We only need to see that one clause is undecided to know if any are undecided.
            anyUndecidedClause = True
    if not anyUndecidedClause:
        # If no clauses are UNSAT and no clauses are undecided,
        # then all clauses are SAT and the whole function is SAT!
        return assignments # SAT

    # At this point, at least one of the clauses is undecided.
    # Choose a literal to try to assign to 1 or to 0...
    # And try those options out by branching recursively.
    xi: int|None = decide_literal(clauses, assignments)
    if not xi:
        # There are no undecided literals, so we can't make any more decisions.
        # This means that the function is UNSAT.
        return {}
    assert(assignments[xi] is None)
    # Try xi=1
    assignments[xi] = 1
    if (result := dpll(clauses, assignments)):
        # SAT
        return result
    # Try xi=0
    assignments[xi] = 0
    if (result := dpll(clauses, assignments)):
        # SAT
        return result
    # If both xi=1 and xi=0 failed, then this whole recursive branch is UNSAT.
    # So return UNSAT to the callee (probably the previous recursive call).
    assignments[xi] = None # undo the decision
    return {} # UNSAT


def dpll_with_stack(clauses: list[Clause]):# -> dict[int,Any]:
    print('Calling dpll_with_stack...')
    print('clauses are ', clauses)
    assignments = all_undecided(clauses)

    # Push some initial decisions onto the stack
    stack = []
    xi = decide_literal(clauses, assignments)
    if not xi:
        return {}
    stack.append(('try', xi, 0))
    stack.append(('try', xi, 1))

    while stack:
        print('stack:', stack)
        (action, xi, value) = stack.pop()
        print(action, "xi:", xi, "value:", value)
        assignments[xi] = value
        if action == "restore":
            # Undo the value for xi
            continue
        stack.append(('restore', xi, assignments[xi]))
        anyUndecidedClause: bool = False
        for clause in clauses:
            value = clause_value(clause, assignments)
            if value == UNSAT:
                # If any clause is UNSAT, then the whole function is UNSAT.
                # This branch is UNSAT, so we should backtrack and try the other value for xi.
                print('UNSAT branch')
                continue
            elif value == UNDECIDED:
                # We only need to see that one clause is undecided to know if any are undecided.
                print('found undecided clause')
                anyUndecidedClause = True
        if anyUndecidedClause:
            new_xi = decide_literal(clauses, assignments)
            if not new_xi:
                # There are no undecided literals, so we can't make any more decisions.
                print('UNSAT due to no undecided literals')
                continue
            stack.append(('try', new_xi, 0))
            stack.append(('try', new_xi, 1))
        else:
            # If no clauses are UNSAT and no clauses are undecided,
            # then all clauses are SAT and the whole function is SAT!
            print('returning SAT')
            return assignments # SAT

    # If this point is reached, UNSAT
    print('returning UNSAT')
    return {}


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


def test_clause_value():
    '''
    Test the clause_value() function
    '''
    # test one positive literal (x1)
    c = make_CNF_clause([1], [])

    # postive literal is set to 1
    v = clause_value(c, {1:1})
    assert(v == SAT)

    # Setting clause with only one literal to 0
    v = clause_value(c, {1:0})
    assert(v == UNSAT)

    # The only literal is undecided
    v = clause_value(c, {1:None})
    assert(v == UNDECIDED)

    # Test one negative literal (~x1)
    c = make_CNF_clause([], [1])

    # assign the literal to 1, which makes the clause false
    v = clause_value(c, {1:1})
    assert(v == UNSAT)

    # assign the literal to 0, which makes the clause true
    v = clause_value(c, {1:0})
    assert(v == SAT)

    # The only literal is undecided
    v = clause_value(c, {1:None})
    assert(v == UNDECIDED)

    # Test a clause with 2 literals
    c = make_CNF_clause([1,2], [])
    testPairs2 = [
        ({1:1, 2:1}, SAT),
        ({1:1, 2:0}, SAT),
        ({1:0, 2:1}, SAT),
        ({1:0, 2:0}, UNSAT),
        ({1:None, 2:None}, UNDECIDED),
        ({1:0, 2:None}, UNDECIDED),
        ({1:None, 2:0}, UNDECIDED),
        ({1:1, 2:None}, SAT),
        ({1:None, 2:1}, SAT),
    ]
    for assignment, expected in testPairs2:
        v = clause_value(c, assignment)
        try:
            assert(v == expected)
        except AssertionError:
            print(f"Failed test with assignments {assignment} and expected {expected} but got {v}")
            exit(1)

    # Test a clause with 3 positive literals
    # (not testing all combinations of 0,1, and None)
    c = make_CNF_clause([1,2,3], [])
    testPairs3 = [
        ({1:1, 2:1, 3:1}, SAT),
        ({1:1, 2:1, 3:0}, SAT),
        ({1:1, 2:0, 3:1}, SAT),
        ({1:1, 2:0, 3:0}, SAT),
        ({1:0, 2:1, 3:1}, SAT),
        ({1:0, 2:1, 3:0}, SAT),
        ({1:0, 2:0, 3:1}, SAT),
        ({1:0, 2:0, 3:0}, UNSAT),
        ({1:0, 2:1, 3:None}, SAT),
        ({1:None, 2:None, 3:1}, SAT),
        ({1:None, 2:0, 3:None}, UNDECIDED),
    ]
    for assignment, expected in testPairs3:
        v = clause_value(c, assignment)
        try:
            assert(v == expected)
        except AssertionError:
            print(f"Failed test with assignments {assignment} and expected {expected} but got {v}")
            exit(1)


def test_dpll():
    # test no clauses (just make sure it doesn't crash)
    assert(dpll([]) == {})

    # Test a single clause with one positive literal (SAT)
    clauses = [make_CNF_clause([1], [])] # (x1)
    result = dpll(clauses)
    assert(result)
    assert(result[1] == 1)
    assert(result == {1:1})

    # Test a single clause with one negative literal (SAT)
    clauses = [make_CNF_clause([], [1])] # (~x1)
    result = dpll(clauses)
    assert(result)
    assert(result[1] == 0)
    assert(result == {1:0})

    # Test conflicting clauses (UNSAT)
    clauses = [make_CNF_clause([1], []), make_CNF_clause([], [1])] # (x1).(~x1)
    result = dpll(clauses)
    assert(result == {})

    # Test 2 clauses
    clauses = [make_CNF_clause([1], []), make_CNF_clause([2], [])] # (x1).(x2)
    result = dpll(clauses)
    assert(result)
    assert(result == {1: 1, 2: 1})

    # Test 2 clauses (one has a positive literal, one is negative literal)
    clauses = [make_CNF_clause([1], []), make_CNF_clause([], [2])] # (x1).(~x2)
    result = dpll(clauses)
    assert(result)
    assert(result == {1: 1, 2: 0})

    # Test 2 clauses (both negative literals)
    clauses = [make_CNF_clause([], [1]), make_CNF_clause([], [2])] # (~x1).(~x2)
    result = dpll(clauses)
    assert(result)
    assert(result == {1: 0, 2: 0})


def main():
    if True:
        # Run tests
        print('Running tests...')
        test_clause_value()
        test_dpll()
        print('All tests passed.')

    with open(args.file, "r") as file:
        function1 = file.readline()
        if args.xor:
            function2 = file.readlines()[1]
        
    print('Parsing SOP input:', function1)
    sop = parse_SOP_string(function1)
    print('Parsed result:', '+'.join([x.__str__(False) for x in sop]))
    print('Converting to CNF, clauses are:')
    cnf = convert_SOP_to_CNF(sop)
    print(".".join([str(c) for c in cnf])) # print clause list

    result = dpll(cnf)
    if result:
        print("Function is SAT with these assignments:")
        printAssignments(result)
    else:
        print("Function is UNSAT")


if __name__ == "__main__":
    main()