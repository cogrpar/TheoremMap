import networkx as nx
import sys
import unittest
sys.path.append('../TheoremMap')
from leanInterface import *
from pythonComponent import generateDerivationGraph


class TestingGenerateDerivationGraph(unittest.TestCase):
    def testEmpty(self):
        # test the case where objectList is empty
        emptyG = nx.DiGraph()
        emptyInput = LeanDef('object_list', 'List (List String)', [])
        self.assertTrue(nx.utils.misc.graphs_equal(generateDerivationGraph(emptyInput), emptyG))

    def testSimple(self):
        # test the case with simple objectList
        G = nx.DiGraph()
        G.add_node("p")
        G.add_node("q")
        G.add_edge("p", "q", objectName="a", importPath="import1")
        G.add_node("p → q")
        G.add_node("q → p ∧ q")
        G.add_node("p ∧ q")
        G.add_edge("p → q", "p ∧ q", objectName="b", importPath="import2")
        G.add_edge("p", "q → p ∧ q", objectName="b", importPath="import2")
        emptyInput = LeanDef('object_list', 'List (List String)', 
                             [["a", "p → q", "import1"],
                              ["b", "p → q → p ∧ q", "import2"]])
        self.assertTrue(nx.utils.misc.graphs_equal(generateDerivationGraph(emptyInput), G))

# the program begins below
if __name__ == '__main__':
    unittest.main()