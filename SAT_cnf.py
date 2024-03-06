
class Clause:
    """
    Clause Class. Reference https://www.geeksforgeeks.org/python-linked-list/
    """
    def __init__(self, number, data):
        #Assign number to the clause
        self.number = number
 
        #Assign data to clause. Should be the CNF clause. Possibly dictionary?
        self.data = data
       
        #Initalize next as null
        self.next = None
 
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
Example:
  createClause([1,2,4], [3,5]) represents the CNF clause "(x1 + x2 + x3' + x4 + x5')"
Izak is responsible for this function.
'''
def createCNFClause(ones: list, zeros: list) -> Clause:
    ones = set(ones)
    zeros = set(zeros)
    for var_i in ones:
        if var_i in zeros:
            raise ValueError(f"variable index {var_i} should not be in the `ones` set and the `zeros` set")
    clause = dict()
    for var_i in ones:
        clause[var_i] = 1
    for var_i in zeros:
        clause[var_i] = 0
    return Clause(number=0, data=clause)
                


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
