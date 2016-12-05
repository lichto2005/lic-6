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

//ostream& operator<<(ostream& ostr, const Graph& g)
//{
//	// print operator for Graph
//
//	ostr << "-------------------Vertices-------------------" << endl;
//	// iterate over all vertices
//	NodeIteratorRange vitR = vertices(g);
//	for (NodeIterator it = vitR.first; it != vitR.second; it++)
//	{
//		// print all information for each vertex
//		ostr << "Marked: " << g[*it].marked << endl << "Pred: " << g[*it].pred << endl;
//		ostr << "Visited: " << g[*it].visited << endl << "Weight: " << g[*it].weight << "\n\n";
//	}
//
//	ostr << "-------------------Edges-------------------" << endl;
//	// iterate over all edges
//	EdgeIteratorRange eitR = edges(g);
//	for (EdgeIterator it = eitR.first; it != eitR.second; it++)
//	{
//		// print all information for each edge
//		ostr << "Weight: " << g[*it].weight << endl;
//		ostr << "Marked: " << g[*it].marked << endl;
//		ostr << "Visited: " << g[*it].visited << endl;
//		ostr << source(*it, g) << " --" << g[*it].weight << "--> " << target(*it, g) << endl << endl;
//	}
//	return ostr;
//}

int connectedComponents(const Graph &g1)
{
	Graph g = g1;
	int connectedC = 0;
	clearVisited(g);
	clearMarked(g);

	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		g[*n].pred = LargeValue;
	}

	stack<Vertex> s;
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		if (g[*n].visited == true) continue;
		connectedC += 1;
		s.push(*n);

		bool vertAdded;
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
		total_cost += g[*it].weight;
	}
	ostr << endl;

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

// function that adjusts the estimate of the weight of node v using the edge between u and v
void relax(Graph &g, Vertex u, Vertex v)
{
	// get edge check if it exists
	Edge e = edge(u, v, g);
	if (e.second)
	{
		// if the current weight is higher than weight of u + weight of edge
		if (g[v].weight > g[u].weight + g[e.first].weight)
		{
			// adjust current weight to new value
			g[v].weight = g[u].weight + g[e.first].weight;
			// change predecessor
			g[v].pred = u;
		}
	}
}

// function which uses an edge e to perform the relax
// this function was added to handle multiple out_edges coming from one node
void relax_edge(Graph &g, Graph::edge_descriptor e)
{
	// from edge, get u and v
	Vertex u = source(e, g);
	Vertex v = target(e, g);
	// get edge weight
	int w = g[e].weight;
	// if current weight is more than u + w
	if (g[v].weight > g[u].weight + w)
	{
		// adjust current value and change predecessor
		g[v].weight = g[u].weight + w;
		g[v].pred = u;
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

bool isCyclic(Graph &g)
{
	clearVisited(g);

	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		g[*n].pred = LargeValue;
	}

	Vertex start = *vitR.first;
	g[start].visited = true;

	stack<Vertex> s;
	s.push(start);

	bool vertAdded;
	while (s.size() > 0)
	{
		vertAdded = false;
		Vertex u = s.top();
		AdjIteratorRange aitR = adjacent_vertices(u, g);
		for (AdjIterator v = aitR.first; v != aitR.second; ++v)
		{
			Vertex v_vert = *v;
			if (g[*v].visited == true && !(g[u].pred == *v || g[*v].pred == u))
				return true;
			if (g[*v].visited == true)
				continue;
			else
			{
				g[*v].visited = true;
				g[*v].pred = u;
				s.push(*v);
				vertAdded = true;
				break;
			}
		}
		if (!vertAdded)
		{
			s.pop();
			if (s.size() == 0)
			{
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

bool isConnected(Graph &g)
{
	clearVisited(g);
	clearMarked(g);

	NodeIteratorRange vitR = vertices(g);
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		g[*n].pred = LargeValue;
	}

	Vertex start = *vitR.first;
	g[start].visited = true;

	stack<Vertex> s;
	s.push(start);

	bool vertAdded;
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
	for (NodeIterator n = vitR.first; n != vitR.second; ++n)
	{
		if (g[*n].visited == false) return false;
	}
	return true;
}

void findSpanningForest(Graph &g, Graph &sf)
{
	clearMarked(g);
	sf = Graph(num_vertices(g));
	EdgeIteratorRange eitR = edges(g);
	for (EdgeIterator e = eitR.first; e != eitR.second; e++)
	{
		Vertex u = source(*e, g);
		Vertex v = target(*e, g);
		int weight = g[*e].weight;
		if (g[u].marked == false || g[v].marked == false)
		{
			g[u].marked = true;
			g[v].marked = true;
			Edge new_e = add_edge(u, v, sf);
			sf[new_e.first].weight = weight;
			new_e = add_edge(v, u, sf);
			sf[new_e.first].weight = weight;
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
	}
	catch (fileOpenError e)
	{
		//noop
	}
}