
#include <iostream>
#include <boost/graph/adjacency_list.hpp>

#include "vf2.hpp"


using namespace boost;
using namespace graph_alg;

typedef adjacency_list<vecS,vecS,
		       //bidirectionalS
		       undirectedS
		       > Graph;
typedef typename graph_traits<Graph>::vertex_descriptor VDescr;



////////////////////////////////////////////////
// boost graph labeling
typedef char label_type;
//                    0    1    2    3    4    5    6    7    8
label_type g1v[9] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'j' };
label_type g2v[9] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'j' };
bool vc(const Graph&, const Graph&, VDescr v1, VDescr v2) { return g1v[v1] == g2v[v2]; }


int main()
{
    Graph g1(9);
    Graph g2(9);

    add_edge(0, 1, g1);
    add_edge(1, 2, g1);
    add_edge(2, 0, g1);
    add_edge(1, 3, g1);
    add_edge(3, 4, g1);
    add_edge(4, 2, g1);
    add_edge(5, 0, g1);
    add_edge(5, 1, g1);
    add_edge(6, 1, g1);
    add_edge(6, 3, g1);
    add_edge(7, 4, g1);
    add_edge(7, 3, g1);
    add_edge(8, 3, g1);
    add_edge(8, 7, g1);



    add_edge(3, 0, g2);
    add_edge(3, 4, g2);
    add_edge(0, 4, g2);
    add_edge(1, 4, g2);
    add_edge(0, 2, g2);
    add_edge(1, 2, g2);
    add_edge(5, 3, g2);
    add_edge(5, 0, g2);
    add_edge(6, 0, g2);
    add_edge(6, 2, g2);
    add_edge(7, 1, g2);
    add_edge(7, 2, g2);
    add_edge(8, 2, g2);
    add_edge(8, 7, g2);


    graph_isomorphism_all(g1, g2);
}

