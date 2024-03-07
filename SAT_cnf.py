import re
from typing import Any


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

        # Set to confirm if clause is SAT
        self.isSAT: bool = False

        self.isUnitClause = False

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

    [Izak is responsible for this function.]
    '''
    # Get the last/highest variable index value, xi:
    max_var_i: int = max([max(term.data.keys()) for term in productTerms])
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


def check_SAT_clause(clause: list[Clause]):
    '''
    Function to check if given list of clause is SAT or UNSAT.
    Takes in a list of Clause objects and traverses through the list. A clause is SAT one literal is 1.
    Function returns True if all clauses are SAT
    If UNSAT, function returns False and a clause list of UNSAT clauses
    '''
    # Check to see if clauses are SAT. Store UNSAT clauses in list. Not sure if this is needed
    unsat_clauses: list[Clause] = []
    is_function_sat: bool = True
    for clauses in range(len(clause)):
        current_clause = clause[clauses]
        #Default for .isSAT is false. Not sure if this memeber is needed
        if current_clause.isSAT is not True:
            print(current_clause.data)
            tmp_val = list(current_clause.data.values())
            for i in range(len(tmp_val)):
                max_val = len(tmp_val) - 1
                end_of_list_flag = False
                if tmp_val[i] == 1:
                    current_clause.isSAT = True
                    print(f"Clause {clause[clauses]} is SAT")
                    end_of_list_flag = True
                    break
                if max_val == i and end_of_list_flag == False:
                    print(f"Clause {clause[clauses]} is UNSAT")
                    is_function_sat = False
                    unsat_clauses.append(clause[clauses])
                    break
                    
                
    return is_function_sat, unsat_clauses



def dpll(clauses: list[Clause]):
    '''
    Use DPLL algorithm to find unit clauses and solve
    '''
    # Find the max term to make sure to never change value from 1 to 0
    max_term = 0 
    for clause in clauses:
        # Find max terms from list of clauses. Use literal number names for reference
        terms = re.findall(r'\d+', repr(clause))
        tmp_max = max(terms)
        if max_term < int(tmp_max):
            max_term = int(tmp_max)
    for i in range(len(clauses)):
        current_clause = clauses[i]
        if current_clause.isUnitClause is False:
            unit_clause = current_clause
            print(unit_clause.data)
            terms = re.findall(r'\d+', unit_clause.__repr__())
            for i in terms:
                # if i == max term, iterate over
                if int(i) == max_term:
                    break
                # Test to see if this assignment works. Pretty much just the complement of the literals.
                # Need to figure out if the .isSAT member is really needed. Probably not
                if unit_clause.data[int(i)] == 0:
                    unit_clause.data[int(i)] = 1
                    unit_clause.isSAT = False
                else:
                    unit_clause.data[int(i)] = 0
                    unit_clause.isSAT = False
                print(unit_clause.data)
        
    

sop_str = "x1.x3 + ~x1.x2"
print('Parsing SOP input:', sop_str)
sop = parse_SOP_string(sop_str)
print('Parsed result:', str(sop))
print('Converting to CNF, clauses are:')
cnf = convert_SOP_to_CNF(sop)
print(".".join([str(c) for c in cnf])) # print clause list
n = max(cnf[-1].data.keys()) # quick and overly specific way to do this
print(f"The output variable is x{n} and must be set to 1.")

check_SAT_clause(cnf)
dpll(cnf)
check_SAT_clause(cnf)
