import networkx as nx
import sys
import unittest
sys.path.append('../TheoremMap')
from leanInterface import *
from pythonComponent import generateDerivationGraph, populateGraphWithAndJoinedArgs


class TestingGenerateDerivationGraph(unittest.TestCase):
    def testEmpty(self):
        # test the case where objectList is empty
        emptyG = nx.DiGraph()
        emptyInput = LeanDef('object_list', 'List (List String)', [])
        self.assertTrue(nx.utils.misc.graphs_equal(generateDerivationGraph(emptyInput), emptyG))

    def testSimple(self):
        # test the case with simple objectList
        G = nx.DiGraph()
        G.add_node('p')
        G.add_node('q')
        G.add_edge('p', 'q', objectName='a', importPath='import1')
        G.add_node('q → p ∧ q')
        G.add_edge('p', 'q → p ∧ q', objectName='b', importPath='import2')
        
        emptyInput = LeanDef('object_list', 'List (List String)', 
                             [['a', 'p → q', 'import1'],
                              ['b', 'p → q → p ∧ q', 'import2']])
        self.assertTrue(nx.utils.misc.graphs_equal(generateDerivationGraph(emptyInput), G))

class TestingPopulateGraphWithAndJoinedArgs(unittest.TestCase):
    def testEmpty(self):
        # test the case where objectList is empty
        emptyG = nx.DiGraph()
        self.assertTrue(nx.utils.misc.graphs_equal(populateGraphWithAndJoinedArgs(emptyG), emptyG))

    def testModerate(self):
        # test with a slightly more complex derivation graph
        G = nx.DiGraph()
        G.add_node('p')
        G.add_node('q')
        G.add_node('j')
        G.add_node('k')
        G.add_edge('p', 'q → j → k', objectName='a', importPath='import1')
        G2 = G.copy()
        G2.add_node('p ∧ q')
        G2.add_node('j → k')
        G2.add_edge('p ∧ q', 'j → k', 
                   objectName='''(fun (args : p ∧ q) =>
                        a (args.left) (args.right))''',
                   importPath='import1')
        G2.add_node('p ∧ q ∧ j')
        G2.add_edge('p ∧ q ∧ j', 'k', 
                   objectName='''(fun (args : p ∧ q ∧ j) =>
                        a (args.left) (args.right.left) (args.right.right))''',
                   importPath='import1')
        self.assertTrue(nx.utils.misc.graphs_equal(populateGraphWithAndJoinedArgs(G), G2))

# the program begins below
if __name__ == '__main__':
    unittest.main()