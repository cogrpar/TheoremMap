# this file implements the high level control of generating the theorem map in python
# most of the actual work is done in lean 4, this file just calls lean 4 functions stored in LeanBackend.lean
import generateObjectList
import json
from leanInterface import *
import pickle
import matplotlib.pyplot as plt
import networkx as nx
import os
    

# ---------- lean interfacing functions ----------

# below is the python wrapped split_terms function
splitTerms = LeanDef('split_terms')
def splitTermsCall (inpt : LeanTheorem | LeanDef, delim : LeanTheorem | LeanDef) -> tuple[str, list]:
    num_open = 0 # keep track of num of open and closed parentheses
    num_closed = 0
    expression = inpt.value
    delim = delim.value.strip().strip('"')
    check = ' ' * len(delim) # check all sequences of characters within the expression with the same length as delim
    current_terms = '' # store each term before reaching an instance of delim
    split = [] # list of split terms
    for char in range(len(expression)):
        if expression[char] in ['(', '[', '{']:
            num_open += 1
        elif expression[char] in [')', ']', '}']:
            num_closed += 1
        check = check[1:] + expression[char] if len(check) > 1 else expression[char]
        if (check == delim and num_open == num_closed):
            split.append(current_terms[:-(len(check)-1)] if len(check) > 1 else current_terms)
            current_terms = ''
        elif char == len(expression)-1:
            current_terms += expression[char]
            split.append(current_terms)
        else:
            current_terms += expression[char]
    return ('List String', split)
splitTerms.overrideFunctionality(splitTermsCall)

# below is the python wrapped remove_redundant_parentheses function
removeRedundantParentheses = LeanDef('remove_redundant_parentheses')

# below is the python wrapped lean string storing the implies character
impStr = LeanDef('imp_str')

# below is a LeanDef that that takes two lean4 propositions and returns a bool
# the bool is true if lean can prove they are equal using 'rfl' and false otherwise
# the functionality of the object call is implemented in python not lean
checkPropsEq = LeanDef('check_props_eq', 'Prop → Prop → Bool', 
                       '-- checks if the two passed input props are equivalent (functionality implemented in python not lean)\nsorry')
def checkPropsEqCall (prop1 : LeanTheorem | LeanDef, prop2 : LeanTheorem | LeanDef) -> tuple[str, bool]:
    # running the below script will cause lean to throw an error if the rfl tactic fails to prove that the two passed props are equal
    check = runLeanString(f'''
        import LeanBackend
        {' '.join(f'import {package}' for package in prop1.requiredImports)}
        {' '.join(f'import {package}' for package in prop2.requiredImports)}
        def {prop1.name} := {prop1.value}
        def {prop2.name} := {prop2.value}
        def checkPropsEq : {prop1.name} = {prop2.name} := rfl
    ''')
    # check for an error and return false, otherwise return true
    if 'type mismatch' in check:
        return ('Bool', False)
    return ('Bool', True)
checkPropsEq.overrideFunctionality(checkPropsEqCall)

# this function produces a derivation graph for a given object list
def generateDerivationGraph(objectList):
    G = nx.DiGraph()
    seenTypes = set()
    for object in objectList.value:
        objectName, objectType, objectImportPath = object
        terms = splitTerms(LeanDef('object', 'String', objectType.replace('\n', ' ')), impStr)[1]
        # generate all possible binary splits of the object terms and add them to the map
        if len(terms) == 1: # add all non input types as nodes
            if not terms[0].strip() in seenTypes: # new type
                seenTypes.add(terms[0].strip())
            G.add_node(terms[0].strip())
        else:
            for i in range(len(terms)-1):
                possibleSplit = terms[:i+1], terms[i+1:]
                possibleSplit = ' → '.join(i.strip() for i in possibleSplit[0]), ' → '.join(i.strip() for i in possibleSplit[1])
                # add a node for each side of the split
                for i in range(2):
                    if not possibleSplit[i] in seenTypes: # new type
                        seenTypes.add(possibleSplit[i])
                        G.add_node(possibleSplit[i])
                # add a directional edge between the nodes
                G.add_edge(possibleSplit[0], possibleSplit[1], objectName=objectName, importPath=objectImportPath)

    return G

# the program begins below
if __name__ == '__main__':
    ver = LeanDef('version')

    # generate the object list if the objectList.json file does not exist
    if not os.path.exists('./objectList.json'):
        print('generating objectList.json, this process could take a while...')
        # get the lean toolchain folder because we want to analyze the lean code base itself
        with open('./lean-toolchain') as t:
            home_directory = os.path.expanduser('~')
            toolchain = os.path.join(home_directory, '.elan/toolchains/', f'leanprover--lean4---{t.read().split(":")[1]}'.strip("\n"), 'src/lean/')
        # consider all lean files in the target folders
        objectList = LeanDef('object_list', 'List (List String)', generateObjectList([toolchain, './lake-packages/', './LeanBackend/'])) 
        with open('objectList.json', 'w') as createBackup:
            createBackup.write('{\n\t\"objectList\": ' + json.dumps(objectList.value) + '\n}')
    # otherwise load it if it exists
    else:
        print('found existing object list, continuing...')
        with open('objectList.json', 'r') as fetchBackup:
            objectList = LeanDef('object_list', 'List (List String)', json.load(fetchBackup)['objectList'])

    # generate the derivation graph if the derivationGraph.pickle file does not exist
    if not os.path.exists('derivationGraph.pickle'):
        print('generating derivationGraph.json, this process could take a while...')
        G = generateDerivationGraph(objectList)
        pickle.dump(G, open('derivationGraph.pickle', 'wb'))
    # otherwise load it if it exists
    else:
        print('found existing derivation graph, continuing...')
        G = pickle.load(open('derivationGraph.pickle', 'rb'))

    G = generateDerivationGraph(objectList)

    print(G)

    # clean up by removing the tmp.lean file
    cleanup()
