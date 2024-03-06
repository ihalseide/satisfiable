import re
from typing import Any


class Clause:
    """
    Clause Class. Reference https://www.geeksforgeeks.org/python-linked-list/
    """
    def __init__(self, number, data: dict, isCNF=True):
        #Assign number to the clause
        self.number = number
 
        #Assign data to clause. Should be the CNF clause. Possibly dictionary?
        self.data: dict = data
       
        #Initalize next as null
        self.next: Clause|None = None

        self.isCNF: bool = isCNF

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
 
class ListOfClauses:
    """
    List of Clause class. Will be the linked list to store the clauses. Individual dictionaries used to store each individual clause?
    Referenced https://www.geeksforgeeks.org/python-linked-list/
    """
    def __init__(self):
        self.head = None
 
        #Assign a new node to the beginning of the list
    def pushToBeginning(self, number, newData):
 
        #Call Clause with the passed in data to create the structure and assign it to newClause
        newClause = Clause(number, newData)
       
        #Make the next of the new node the head of the node
        newClause.next = self.head
 
        #Make the head point to the new node
        self.head = newClause
       
        #Insert node to end of list. If in the beginning, insert next to initial head
    def append(self, number, newData):
        """
        Append new node at the end of list. Referended https://www.geeksforgeeks.org/python-linked-list/
        """
        newClause = Clause(number, newData)
        #If at he beginning of the list, insert at head
        if self.head is None:
            self.head = newClause
            return
        #Else, go to the end of the list and insert
        last = self.head
        while (last.next):
            last = last.next
 
        last.next = newClause
 
    def printClauseList(self):
        """
        Print the list of clauses
        """
        tmp = self.head
        while (tmp):
            print("Clause Number: {}\nClause is: {}\n".format(tmp.number, tmp.data))
            tmp = tmp.next
    
    def doComplement(self):
        """
        Find the complement of the individual clauses. Since input is in SoP form, we should only need to do the complement of each variable
        """
        #Start at the beginning. While tmp != None
        tmp = self.head
        while(tmp):
            #Create tmp dictonary
            newDict = {}
            #Traverse through current dictionary in list
            for variable, value in tmp.data.items():
                #If ~x is the literal, then it's complement will be x
                if '~' in variable:
                    tmp_var = variable[1:]
                    tmp_val = value
                    newDict[tmp_var] = tmp_val
                #If x is the literal, then it's complement will be ~x
                else:
                    tmp_var = '~' + variable
                    tmp_val = value
                    newDict[tmp_var] = tmp_val
            #Assign the current node the complement dictionary
            tmp.data = newDict
            tmp = tmp.next
    
    def setBoolNone(self):
            """
            Set the value of the literals to None
            """
            tmp = self.head
            while(tmp):
                newDict = {}
                for variable, value in tmp.data.items():
                    print(variable)
                    newDict.__setitem__(f"{variable}", None)
                tmp.data = newDict
                tmp = tmp.next


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
Returns a list of `Clause`s, but they are product terms, NOT CNF clauses!
[Izak is responsible for this function.]
'''
def parse_SOP_string(text: str) -> list[Clause]:
    terms = text.split('+')
    clauses: list[Clause] = []
    lit_pattern = re.compile(' *(~?) *x([0-9]+)')
    for term in terms: # example: "~x1 x2"
        literals = lit_pattern.findall(term)
        ones = [int(pair[1]) for pair in literals if pair[0]!='~']
        zeros = [int(pair[1]) for pair in literals if pair[0]=='~']
        newClause = make_CNF_clause(ones, zeros)
        newClause.isCNF = False
        clauses.append(newClause)
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
        add_and_gcf(CNF, term.data, and_output_var)
    # Add the CNF clauses from the single OR gate consistency function.
    # The inputs to the OR are all of the AND output variables.
    or_input_vars = range(extra_var_i, extra_var_i + len(productTerms))
    add_or_gcf(CNF, or_input_vars, final_output_var_i)
    # Add the final clause: the fact that the output variable should be 1
    CNF.append(make_CNF_clause(ones=[final_output_var_i], zeros=[]))
    return CNF 


'''
Helper function for convert_SOP_to_CNF()
Given a product term (from SOP form), and it's output variable,
add all of it's required CNF clauses to the `toList`
as determined by the AND gate consistency function.
[Izak is responsible for this function.]
'''
def add_and_gcf(toList: list[Clause], term: dict[int, Any], term_out_var_i: int):
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
Helper function for convert_SOP_to_CNF()
Create the consistency function for the OR gate that occurs in SOP form.
All the input variables are positive, which is why this function is simpler than
the `addAndTermConsistencyFunction`.
'''
def add_or_gcf(toList: list[Clause], or_input_vars, output_var: int):
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


a = ListOfClauses()
dictOfClauses1 = {"x1": 0,
                 "x2": 1,
                 "~x3": 0}

dictOfClauses2 = {"~x1": 1,
                 "x4": 1}

a.pushToBeginning(1, dictOfClauses1)
a.append(2, dictOfClauses2)

a.setBoolNone()
a.doComplement()
a.printClauseList()

sop_str = "x1 + x2 + x3"
print('Parsing SOP input:', sop_str)
sop = parse_SOP_string(sop_str)
print('Parsed result:', str(sop))
print('Converting to CNF, clauses are:')
cnf = convert_SOP_to_CNF(sop)
print(".".join([str(c) for c in cnf])) # print clause list
n = max(cnf[-1].data.keys()) # quick and overly specific way to do this
print(f"The output variable is x{n} and must be set to 1.")