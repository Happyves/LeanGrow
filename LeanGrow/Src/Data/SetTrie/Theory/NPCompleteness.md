
# The minimum weight set-trie problem is NP complete

This solution was found by Kilian Rueß (UTN) a couple of hours after we presented set-tries in a talk!

We can solve minimum vertex cover via minimum set-tries.
Given a graph of edge set E, consider the minimum set-trie for the family of sets that are these edges.
The root-to-leaf paths can only be of two kinds: either the edge is a leaf or one of its endpoints is a parent of multiple child leaves, each having a single point.
Then, for the children of the root, choosing one of the vertices for leaves that are an edge of the graph, and the vertex if the child represents a set of size 1, we get a vertex cover of the graph of size k where k is the number of children of the root.
Conversely, every vertex cover of k vertices corresponds to such a set-trie: add the vertices as children of the root, and the remaing ones as children of the one that covers the edge (if both endpoints are in the cover, choose a single one), to get a set-trie of size k+|E|.
