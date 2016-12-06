#include <iostream>
#include <limits.h>
#include <vector>
#include <list>
#include <fstream>
#include <queue>
#include <stack>

#include "d_except.h"
#include "heapV.h"

#include <boost/graph/adjacency_list.hpp>

using namespace boost;
using namespace std;

#define LargeValue 99999999

struct VertexProperties;
struct EdgeProperties;

typedef adjacency_list<vecS, vecS, bidirectionalS, VertexProperties, EdgeProperties> Graph;
typedef Graph::vertex_descriptor Vertex;
typedef pair<Graph::edge_descriptor, bool> Edge;

struct VertexProperties
{
	Graph::vertex_descriptor pred; // predecessor node
	int weight;
	bool visited;
	bool marked;
};

// Create a struct to hold properties for each edge
struct EdgeProperties
{
	int weight;
	bool visited;
	bool marked;
};

// typedefs for graph elements
typedef pair<Graph::vertex_iterator, Graph::vertex_iterator> NodeIteratorRange;
typedef Graph::vertex_iterator NodeIterator;

typedef pair<Graph::edge_iterator, Graph::edge_iterator> EdgeIteratorRange;
typedef Graph::edge_iterator EdgeIterator;

typedef pair<Graph::adjacency_iterator, Graph::adjacency_iterator> AdjIteratorRange;
typedef Graph::adjacency_iterator AdjIterator;

void clearVisited(Graph &g)
// Mark all nodes in g as not visited.
{
	NodeIteratorRange itR = vertices(g);
	for (NodeIterator it = itR.first; it != itR.second; it++)
	{
		g[*it].visited = false;
	}
}

void setNodeWeights(Graph &g, int w)
// Set all node weights to w.
{
	NodeIteratorRange itR = vertices(g);
	for (NodeIterator it = itR.first; it != itR.second; it++)
	{
		g[*it].weight = w;
	}
}

void clearMarked(Graph &g)
{
	// Mark all nodes as unmarked
	NodeIteratorRange itR = vertices(g);
	for (NodeIterator it = itR.first; it != itR.second; it++)
	{
		g[*it].marked = false;
	}
}

int connectedComponents(const Graph &g1)
{
	// copy graph and setup for traversal
	Graph g = g1;
	int connectedC = 0;
	clearVisited(g);
	clearMarked(g);

	// set all preds to NIL
	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		g[*n].pred = LargeValue;
	}

	stack<Vertex> s;
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		// find an unvisited node and push to stack
		if (g[*n].visited == true) continue;
		// open a new component
		connectedC += 1;
		s.push(*n);

		// perform DFS on component
		while (s.size() > 0)
		{
			Vertex u = s.top();
			s.pop();
			g[u].visited = true;
			AdjIteratorRange aitR = adjacent_vertices(u, g);
			for (AdjIterator v = aitR.first; v != aitR.second; ++v)
			{
				Vertex v_vert = *v;
				if (g[*v].visited == true)
					continue;
				else
				{
					s.push(*v);
				}
			}
		}
		// close component
	}
	return connectedC;
}

ostream& operator<<(ostream& ostr, const Graph& g)
{
	// print operator for Graph

	ostr << "Edges" << endl;
	// iterate over all edges
	int total_cost = 0;
	EdgeIteratorRange eitR = edges(g);
	for (EdgeIterator it = eitR.first; it != eitR.second; it++)
	{
		// print all information for each edge
		ostr << source(*it, g) << " --" << g[*it].weight << "--> " << target(*it, g) << endl;
		// sum weight
		total_cost += g[*it].weight;
	}
	ostr << endl;

	// div by 2 because separate weight for each direction of each edge
	total_cost /= 2;
	ostr << "Total cost: " << total_cost << endl;
	ostr << "Connected Components: " << connectedComponents(g) << endl;

	return ostr;
}

void initializeGraph(Graph &g, ifstream &fin)
	// Initialize g using data from fin.  Set start and end equal
	// to the start and end nodes.
{
	EdgeProperties e;

	int n, i, j;
	int startId, endId;
	fin >> n;
	Graph::vertex_descriptor v;

	// Add nodes.
	for (int i = 0; i < n; i++)
	{
		v = add_vertex(g);
	}

	while (fin.peek() != '.')
	{
		fin >> i >> j >> e.weight;
		add_edge(i, j, e, g);
	}
}

// setup the graph for operation by algorithms
void initializeSingleSource(Graph &g, Vertex s)
{
	// iterate over all nodes
	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator it = vitR.first; it != vitR.second; it++)
	{
		// set pred to a NIL value
		g[*it].pred = LargeValue;
		// set weight to an INF value
		g[*it].weight = LargeValue;
	}
	// set starting node weight to 0
	g[s].weight = 0;
}

// checks for cycles in graph g
// uses DFS
bool isCyclic(Graph &g)
{
	// setup
	clearVisited(g);

	// clear preds
	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		g[*n].pred = LargeValue;
	}

	// add start node to stack
	Vertex start = *vitR.first;
	g[start].visited = true;

	stack<Vertex> s;
	s.push(start);

	// while havent seen all nodes
	bool vertAdded;
	while (s.size() > 0)
	{
		// u is top node
		vertAdded = false;
		Vertex u = s.top();
		// search all adj to u
		AdjIteratorRange aitR = adjacent_vertices(u, g);
		for (AdjIterator v = aitR.first; v != aitR.second; ++v)
		{
			// if node is visited but predecessor, ignore
			// if node is visited and not pred, then have cycle
			Vertex v_vert = *v;
			if (g[*v].visited == true && !(g[u].pred == *v || g[*v].pred == u))
				return true;
			if (g[*v].visited == true)
				continue;
			else
			{
				// if new, mark visited and add to stack
				g[*v].visited = true;
				g[*v].pred = u;
				s.push(*v);
				vertAdded = true;
				break;
			}
		}
		if (!vertAdded)
		{
			// if nothing to add, remove from stack
			s.pop();
			if (s.size() == 0)
			{
				// if stack is empty, add first unvisited node
				for (NodeIterator n = vitR.first; n != vitR.second; ++n)
				{
					if (g[*n].visited == false)
					{
						s.push(*n);
						break;
					}
				}
			}
		}

	}
	return false;
}

// checks if all nodes are connected together in graph g
// uses DFS
bool isConnected(Graph &g)
{
	// setup and mark NIL
	clearVisited(g);
	clearMarked(g);

	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		g[*n].pred = LargeValue;
	}

	// make stack and add first node
	Vertex start = *vitR.first;
	g[start].visited = true;

	stack<Vertex> s;
	s.push(start);

	// while stack is not empty
	while (s.size() > 0)
	{
		// u is top, remove u
		Vertex u = s.top();
		s.pop();
		// mark node visited
		g[u].visited = true;
		// add all adj to stack if unvisited
		AdjIteratorRange aitR = adjacent_vertices(u, g);
		for (AdjIterator v = aitR.first; v != aitR.second; ++v)
		{
			Vertex v_vert = *v;
			if (g[*v].visited == true)
				continue;
			else
			{
				s.push(*v);
			}
		}
		// next u will now become last node added to stack
	}
	// if any node has not been visited after one traversal, graph is unconnected
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		if (g[*n].visited == false) return false;
	}
	// else graph is connected
	return true;
}

// finds a spanning forest connecting all nodes on graph g, returns in graph sf
void findSpanningForest(Graph &g, Graph &sf)
{
	// setup
	clearMarked(g);
	sf = Graph(num_vertices(g));
	// iterate over all edges
	EdgeIteratorRange eitR = edges(g);
	for (EdgeIterator e = eitR.first; e != eitR.second; e++)
	{
		// find source and target vertices
		Vertex u = source(*e, g);
		Vertex v = target(*e, g);
		// find edge weight
		int weight = g[*e].weight;
		// if either node is not added to the forest
		if (g[u].marked == false || g[v].marked == false)
		{
			// mark as added
			g[u].marked = true;
			g[v].marked = true;
			// add the edge in both directions to the forest
			Edge new_e = add_edge(u, v, sf);
			sf[new_e.first].weight = weight;
			new_e = add_edge(v, u, sf);
			sf[new_e.first].weight = weight;
		}
	}
}

void mstPrim(Graph &g, Graph &sf)
{
	sf = Graph(num_vertices(g));
	
	// setup and mark NIL
	clearVisited(g);
	clearMarked(g);
	vector<Vertex> list2;
	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		list2.push_back(*n);
		g[*n].pred = LargeValue;
		g[*n].weight = LargeValue;
	}
	Vertex start = 0;
	g[start].weight = 0;
	
	heapV<Vertex, Graph> q;
	q.initializeMinHeap(list2, g);
	while (q.size() > 0)
	{
		Vertex u = q.extractMinHeapMinimum(g);
		if (g[u].pred != LargeValue)
		{
			Edge e = edge(u, g[u].pred, g);
			int weight = g[e.first].weight;
			Edge e1 = add_edge(u, g[u].pred, sf);
			Edge e2 = add_edge(g[u].pred, u, sf);
			sf[e1.first].weight = weight;
			sf[e2.first].weight = weight;
		}

		AdjIteratorRange aitR = adjacent_vertices(u, g);
		for (AdjIterator v = aitR.first; v != aitR.second; ++v)
		{
			Vertex vert_v = *v;
			try
			{
				q.getIndex(vert_v);
				Edge e = edge(u, vert_v, g);
				if (g[e.first].weight < g[vert_v].weight)
				{
					g[vert_v].pred = u;
					g[vert_v].weight = g[e.first].weight;
					q.minHeapDecreaseKey(q.getIndex(vert_v), g);
				}
			}
			catch (rangeError e)
			{
				// noop
			}
		}
	}
}

int main()
{
	try
	{
		ifstream fin;

		// Read the graph from the file.
		string fileName;
		cout << "Enter a graph file graphX.txt: ";
		cin >> fileName;
		fin.open(fileName.c_str());
		if (!fin)
		{
			cerr << "Cannot open " << fileName << endl;
			exit(1);
		}

		// create graph from file
		Graph g;
		Vertex start, end;
		initializeGraph(g, fin);
		fin.close();

		cout << "\nInput Graph\n----------------------------\n";
		cout << "Is cyclic: " << isCyclic(g) << endl;
		cout << "Is connected: " << isConnected(g) << endl;

		Graph sf;
		findSpanningForest(g, sf);
		cout << "\nSpanning Forest\n----------------------------\n";
		cout << "Is cyclic: " << isCyclic(sf) << endl;
		cout << "Is connected: " << isConnected(sf) << endl;

		cout << sf;

		mstPrim(g, sf);
		cout << "\nMST Prim\n----------------------------\n";
		cout << "Is cyclic: " << isCyclic(sf) << endl;
		cout << "Is connected: " << isConnected(sf) << endl;

		cout << sf;
	}
	catch (fileOpenError e)
	{
		//noop
	}
}