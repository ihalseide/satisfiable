# Psuedo code for all of the main functions and data structures

'''
function main program
    call get program input
    call SAT solver
'''

'''
function to XOR two functions so we can see if 2 functions are different
'''

'''
function to get program input
    call get boolean function
    call get variable subset
'''

'''
function to parse a SoP input function string and return CNF form 

    I think we can parse the SoP and straightforwardly convert it to CNF form as we go along (if we read a term “~x1.x2” then we know the CNF clause for that term is “x1 + ~x2”, so really you just invert the variables as you go?) 
'''

'''
function SAT solver to find ONE solution 

    Given a list of variables, each variable is either unassigned, zero, or one 

    DPLL algorithm – decide, reduce or something 

    We will want to think of this as a recursive function at first, but because of the Python stack limit, we will probably want to manually implement the recursion with a data stack and a while/for loop instead of literal function-call recursion 

    Because with large enough boolean input functions, the call stack could overflow! 

    But we should only worry about this if it happens, and I’m predicting that it could happen 
'''

# We will need heuristic functions, e.g. for conflict-based learning

'''
function to check for unit clauses for implication 
'''

'''
function SAT solver to find ALL solutions, with a subset of variables 

    Keep track of # of variables and the names of the variables, and which subset of variables are included to be solved for 

    Keep track of learned/additional clauses 

    Using the function that finds ONE and then adds the found solutions as clauses to prevent finding that one again 

    Write the report, using the citations of sources we found 
'''