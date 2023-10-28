import networkx as nx
import sys
import unittest
sys.path.append('../TheoremMap')
from prover import findPath


class TestingFindPath(unittest.TestCase):
    def testEmpty(self):
        # test the case where G is empty
        emptyG = nx.DiGraph()
        self.assertRaises(nx.NodeNotFound, findPath, emptyG, 'p', 'q')

    def testSimple(self):
        # test with simple derivation graph
        G = nx.DiGraph()
        G.add_node('p')
        G.add_node('q')
        G.add_edge('p', 'q', objectName='a', importPath='import1')
        G.add_node('q → p ∧ q')
        G.add_edge('p', 'q → p ∧ q', objectName='b', importPath='import2')
        self.assertEqual(findPath(G, 'p', 'q'), (['import1'], ['a']))
        self.assertEqual(findPath(G, 'p', 'q → p ∧ q'), (['import2'], ['b']))
        self.assertRaises(nx.NetworkXNoPath, findPath, G, 'q', 'q → p ∧ q')

    def testModerate(self):
        # test with a slightly more complex derivation graph
        G = nx.DiGraph()
        G.add_node('p')
        G.add_node('q')
        G.add_edge('p', 'q', objectName='a', importPath='import1')
        G.add_node('q → p ∧ q')
        G.add_edge('p', 'q → p ∧ q', objectName='b', importPath='import2')
        G.add_node('j')
        G.add_edge('p', 'q → j', objectName='c', importPath='import3')
        G.add_node('p ∧ q')
        G.add_edge('p ∧ q', 'j', objectName='(fun (args : p ∧ q) => c (a1.left) (a1.right))', importPath='import3')
        G.add_node('k')
        G.add_edge('q', 'k', objectName='d', importPath='import4')
        self.assertEqual(findPath(G, 'p ∧ q', 'j'), (['import3'], ['(fun (args : p ∧ q) => c (a1.left) (a1.right))']))
        self.assertEqual(findPath(G, 'p', 'k'), (['import1', 'import4'], ['a', 'd']))
        self.assertRaises(nx.NetworkXNoPath, findPath, G, 'j', 'p ∧ q')

# the program begins below
if __name__ == '__main__':
    unittest.main()