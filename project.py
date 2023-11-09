"""
Author: Randall Dickinson and Arwen (cat)
Class: Cpt_S 350
Date: 11.8.2023
"""

from pyeda.inter import *

MAX_NODE = 32

X = bddvars('x', 5)
Y = bddvars('y', 5)
Z = bddvars('z', 5)

# Converts integer to binary string of 5 bits
def convert2Binary(num):
    # Might not matter, but will recursively call itself if the input integer
    # is higher than MAX_NODE
    if num >= MAX_NODE:
        return convert2Binary(num - MAX_NODE)
    binString = ""
    for _ in range(0,5):
        if num % 2 == 1:
            binString = "1" + binString
        else:
            binString = "0" + binString
        num = num // 2
    return binString

# Converts a number to an expression for use in creating a BDD
def convert2Expr(num):
    binString = convert2Binary(num)
    exprString = ""

    # Loop through 5 character string binary representation
    for b, i in zip(binString, range(0, 5)):
        if b == '1': 
            exprString += "X[%s] & " % str(i)
        else:
            exprString += "~X[%s] & " % str(i)

    # Remove extra " & " from the end of the string
    exprString = exprString[0:-3]
    return exprString

"""
Given a number and a variable, createBDD will generate a BDD for the binary
representation of that number. Replace is the switch that determines whether 
X, Y, or Z will be used in the BDD.
"""
def createBDD(replace, num):
    d = convert2Expr(num)

    if replace == "Y":
        d = d.replace("X", "Y")
    elif replace == "Z":
        d = d.replace("X", "Z")

    d = expr2bdd(expr(d)).satisfy_all()
    return list(d)[0]

"""
Given a start node and a replacement character, this function will calculate 
RR2 of that given node. That is, it will calculate all nodes that can be 
reached by the given node in exactly two steps.
"""
def findRR2(start, replace):
    stepString = ""
    for i in range(0,MAX_NODE):
        for j in range(0,MAX_NODE):
            if (start.restrict(createBDD("X",i)).restrict(createBDD(replace,j)).is_one()):
                for k in range(0,MAX_NODE):
                    if (((j + 8) % MAX_NODE) == (k % MAX_NODE) or \
                        (j + 3) % MAX_NODE) == (k % MAX_NODE):
                        stepString = stepString + "{1} & {0} | ".format((convert2Expr(i)),\
                            (convert2Expr(k).replace("X", "Z")))    
    return expr2bdd(expr((stepString[0:-3])))    

# Creates the BDD for even numbers 0 - 31
def make_Even():
    evenString = ""

    for num in range(0,31):
        if num % 2 == 0:                          
            evenString = evenString + "%s | " % convert2Expr(num) 
    return expr2bdd(expr(evenString[0:-3]))


# Creates a BDD of all prime numbers 3 - 31
def make_Prime():
    primeString = ""
    primeList = [2]
    # Loop through all possible values
    for num in range(3, MAX_NODE):
        newPrime = True
        # Checks to see if number is divisible by any other primes
        for x in primeList:
            if (num % x) == 0:
                newPrime = False
                break
        # Insert into primeString for converting to BDD
        if newPrime:
            primeString = primeString + "%s | " % convert2Expr(num)
            primeList.append(num)
    
    return expr2bdd(expr(primeString[0:-3]))

"""
Creates a BDD that includes all possible connections from any node to another 
meeting the criteria as outlined in if condition. Once it finds a node pair 
i,j that satisfy the condition, it converts both to a BDD and replaces the 
X's in j with Y's before adding to the string that will eventually become
the BDD. 
"""
def make_RR():
    rString = ""

    for i in range(0,MAX_NODE):
        for j in range(0,MAX_NODE):
            if ((i + 3) % MAX_NODE) == (j % MAX_NODE) or \
                ((i + 8) % MAX_NODE) == (j % MAX_NODE):
                rString = rString + "{1} & {0} | ".format((convert2Expr(i)),\
                    (convert2Expr(j).replace("X", "Y")))

    return expr2bdd(expr(rString[0:-3]))

"""
This function is pain. finStar represents our final string for RR2* that will 
find all edges that can be reached by a number of jumps that is a multiple of 
two (hint it's all of them). Why? Because of the modulo operator being used for
pairing nodes, the pairing of nodes exists in a loop. Because a loop that
starts at node n will reach node n+1 in 6 jumps (an even number), this process 
can be repeated to reach any node thanks to the looping nature of the primary
conditional for RR. 
"""
def make_Star(RR, RR2):
    finStar = RR2
    sigStar = RR

    while (True):
        sigStar = finStar
        tmpStar = sigStar.restrict(dict(list(finStar.satisfy_all())[0]))
        for x in range(1, len(list(finStar.satisfy_all()))):                
            tmpStar = sigStar.restrict(dict(list(finStar.satisfy_all())[x])) | tmpStar
        finStar = tmpStar | sigStar
        if (not finStar.equivalent(sigStar)):
            return finStar


def main():
    # Create the BDD EVEN
    EVEN = make_Even()   
    # Create the BDD PRIME                                              
    PRIME = make_Prime()      
    # Create the BDD RR                                
    RR = make_RR()                                          

    # Verify that the BDD RR only accepts the correct node pairs
    print("RR(27,3) is %s" %RR.restrict(createBDD("X", 27)).restrict(createBDD("Y", 3)).is_one())  
    print("RR(16,20) is %s" %RR.restrict(createBDD("X", 16)).restrict(createBDD("Y", 20)).is_one())                                                     

    # Verify that the BDD EVEN only accepts even nodes
    print("EVEN(14): is %s" % EVEN.restrict(createBDD("X", 14)).is_one())  
    print("EVEN(13): is %s" % EVEN.restrict(createBDD("X", 13)).is_one())

    # Verify that the BDD PRIME only accepts prime nodes
    print("PRIME(7) is %s" % PRIME.restrict(createBDD("X", 7)).is_one())    
    print("PRIME(2) is %s" % PRIME.restrict(createBDD("X", 2)).is_one())                                                 

    # Create the BDD RR2
    RR2 = findRR2(RR, "Y")

    # Verify that the BDD RR2 only accepts the correct node pairs
    print("RR2(27,6) is %s" % RR2.restrict(createBDD("X", 27)).restrict(createBDD("Z", 6)).is_one())
    print("RR2(27,9) is %s" % RR2.restrict(createBDD("X", 27)).restrict(createBDD("Z", 9)).is_one())
    
    # Create the BDD RR2
    RR2STAR = make_Star(RR, RR2)

    print("RR2*(0,0) %s" % RR2STAR.restrict(createBDD("X", 0)).restrict(createBDD("Z",1)).is_one())
    
    # If you want entertainment, uncomment this out to see the transitive closure RR2*
    # for i in range(0,MAX_NODE):
    #     for j in range(0,MAX_NODE):
    #         print("RR2*(%s,%s) %s" % (i, j, \
    #             RR2STAR.restrict(createBDD("X", i)).restrict(createBDD("Z",j)).is_one()))
    
    count = 0
    # One can use smoothing and compose, or one can embrace the logic
    for i in range(0,MAX_NODE):
        if (PRIME.restrict(createBDD("X", i)).is_one()):
            count = count + 1
            statementA = False
            for j in range(0,MAX_NODE):
                if EVEN.restrict(createBDD("X", j)).is_one() and \
                RR2STAR.restrict(createBDD("X", i)).restrict(createBDD("Z",j)).is_one():
                    statementA = True
                    break
            if statementA == False:
                break
    
    print("Statement A is proven %s accross all %s elements of BDD PRIME" % (statementA, count))
    # <drops microphone>

if __name__ == '__main__':
    main()