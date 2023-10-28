# this is a simple theorem prover that uses the theorem map
import networkx as nx

# the theorem prover works by finding a path between nodes in the derivation graph (if possible)
# if a path is discovered, the theorems corresponding to each edge along the way can be applied
# they will by definition map from the desired premises to the desired conclusion

# produces a list of edge names that correspond to path from input node to output node
def findPath(G : nx.DiGraph, inputType : str, outputType : str) -> list[str]:
    imports = [] # will store list of imports for the required theorems
    theorems = [] # will store list of theorems in the order they must be applied
    path = nx.astar_path(G, inputType, outputType)

    # get the names of all theorems (edges) along the path
    prevNode = path[0]
    for node in path[1:]:
        edge = G.get_edge_data(prevNode, node)
        theorems.append(edge['objectName'])
        imports.append(edge['importPath'])
        prevNode = node

    return imports, theorems