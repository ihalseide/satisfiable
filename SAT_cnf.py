import re


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
def createCNFClause(ones: set[int]|list[int], zeros: set[int]|list[int]) -> Clause:
    ones = set(ones)
    zeros = set(zeros)
    for var_i in ones:
        if var_i in zeros:
            raise ValueError(f"variable index {var_i} should not be in both the `ones` set and the `zeros` set")
    clause = dict()
    for var_i in ones:
        clause[var_i] = 1
    for var_i in zeros:
        clause[var_i] = 0
    return Clause(number=0, data=clause)


'''
Parses a Sum-of-Products boolean function string.
Returns a list of `Clause`s, but they are product terms, NOT CNF clauses!
[Izak is responsible for this function.]
'''
def parseSOPString(text: str) -> list[Clause]:
    terms = text.split('+')
    clauses: list[Clause] = []
    lit_pattern = re.compile(' *(~?) *x([0-9]+)')
    for term in terms: # example: "~x1 x2"
        literals = lit_pattern.findall(term)
        ones = [int(pair[1]) for pair in literals if pair[0]!='~']
        zeros = [int(pair[1]) for pair in literals if pair[0]=='~']
        newClause = createCNFClause(ones, zeros)
        newClause.isCNF = False
        clauses.append(newClause)
    return clauses


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

assert(createCNFClause([1],[2]))
print('The `createCNFClause` worked')


# Do some little tests with the parseSOPString() function
testSOPs = [
    "x0",
    " x5",
    "~x1",
    "~ x1",
    "~x1 . ~ x4",
    "x1 . x2 + x3",
    "~ x1 ~ x3 + x5",
    "x1 . ~x2 + ~x3.x1",
    ]
for s in testSOPs:
    terms = [str(t) for t in parseSOPString(s)]
    result = " + ".join(terms)
    print(f"parsing \"{s}\"\n--> \"{result}\"")