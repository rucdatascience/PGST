// PGST.cpp : This file contains the 'main' function. Program execution begins and ends there.

#include <iostream>
#include <iomanip>
#include <fstream>
#include <ctime>
#include <cstdint>
#include <cstdlib>
#include <numeric>
#include <string>
#include <list>
#include <vector>
#include <tuple>
#include <algorithm>
#include <iterator>
#include <chrono>
#include <typeinfo>
#include <unordered_set>
#include <unordered_map>
#include <climits>
#include <math.h>
#include <thread>
#include <chrono>
using namespace std;

/*header files in the Boost library: https://www.boost.org/ */
#include <boost/random.hpp>
boost::random::mt19937 boost_random_time_seed{ static_cast<std::uint32_t>(std::time(0)) };

/*some other header files*/
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_connected_components.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_extract_subgraph.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_PLL.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_merge_graph_hash_of_mixed_weighted.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_nw_ec_normalization.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_PLL_labels.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_binary_save_read.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_graph1_is_graph2.h>
#include <print_items.h>
#include <ThreadPool.h>
#include <copy_items.h>
#include <math/permutations_ys.h>
#include <text mining/string_is_number.h>
#include <text mining/parse_substring_between_pairs_of_delimiters.h>
#include <text mining/parse_substring_between_two_unique_delimiters.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_ec_update_pairwise_jaccard_distance.h>
#include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_generate_random_connected_graph.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_generate_random_groups_of_vertices.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_read_for_GSTP.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_save_for_GSTP.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_PLL.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_PrunedDPPlusPlus.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_DPBF_only_ec.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_breadth_first_search_a_set_of_vertices.h>
#include <graph_v_of_v_idealID/graph_v_of_v_idealID_MST_postprocessing.h>




/*some basic codes*/

#pragma region
int find_g_min(graph_hash_of_mixed_weighted& group_graph, std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|T|)*/

	int g_min;
	int g_min_size = INT_MAX;

	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int x = graph_hash_of_mixed_weighted_adjacent_vertices_size(group_graph, *it);
		if (g_min_size > x) {
			g_min_size = x;
			g_min = *it;
		}
	}

	return g_min;

}
#pragma endregion find_g_min

#pragma region
bool there_is_a_feasible_PGST_in_this_cpn(graph_hash_of_mixed_weighted& cpn, graph_hash_of_mixed_weighted& group_graph, std::unordered_set<int>& group_vertices, double b) {

	/*assume that cpn is a connected graph*/

	for (auto it = group_vertices.begin(); it != group_vertices.end(); it++) {
		int g = *it;
		double p_g_not_coverred = 1;
		bool covered = false;
		for (auto it2 = cpn.hash_of_vectors.begin(); it2 != cpn.hash_of_vectors.end(); it2++) {
			int v = it2->first;
			if (graph_hash_of_mixed_weighted_contain_edge(group_graph, v, g)) {
				double p_g_v = graph_hash_of_mixed_weighted_edge_weight(group_graph, v, g);
				p_g_not_coverred = p_g_not_coverred * (1 - p_g_v);
				if (1 - p_g_not_coverred >= b) {
					break;
				}
			}
		}
		if (1 - p_g_not_coverred < b) {
			return false;
		}
	}

	return true;

}
#pragma endregion there_is_a_feasible_PGST_in_this_cpn

#pragma region
int find_g_min_graph_v_of_v_idealID(graph_v_of_v_idealID& group_graph, std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|T|)*/

	int g_min;
	int g_min_size = INT_MAX;

	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int x = group_graph[*it].size();
		if (g_min_size > x) {
			g_min_size = x;
			g_min = *it;
		}
	}

	return g_min;

}
#pragma endregion find_g_min_graph_v_of_v_idealID

#pragma region
bool this_is_a_feasible_PGST_graph_v_of_v_idealID(graph_hash_of_mixed_weighted& solu, graph_v_of_v_idealID& group_graph, std::unordered_set<int>& group_vertices, double b) {

	/*time complexity O(|V_solu|+|E_solu|)*/
	if (graph_hash_of_mixed_weighted_connected_components(solu).size() != 1) {
		cout << "this_is_a_feasible_PGST: solu is disconnected!" << endl;
		return false;
	}

	for (auto it = group_vertices.begin(); it != group_vertices.end(); it++) {
		int g = *it;
		double p_g_not_coverred = 1;
		bool covered = false;
		for (auto it2 = solu.hash_of_vectors.begin(); it2 != solu.hash_of_vectors.end(); it2++) {
			int v = it2->first;
			if (graph_v_of_v_idealID_contain_edge(group_graph, v, g)) {
				double p_g_v = graph_v_of_v_idealID_edge_weight(group_graph, v, g);
				p_g_not_coverred = p_g_not_coverred * (1 - p_g_v);
			}
		}
		double p_g_coverred = 1 - p_g_not_coverred;
		if (p_g_coverred < b) {
			cout << "this_is_a_feasible_PGST: a group is not satisfactorily covered!" << endl;
			return false;
		}
	}

	return true;

}
#pragma endregion this_is_a_feasible_PGST_graph_v_of_v_idealID

#pragma region
bool there_is_a_feasible_PGST_in_this_cpn_graph_v_of_v_idealID(vector<int>& cpn_vertices, graph_v_of_v_idealID& group_graph, std::unordered_set<int>& group_vertices, double b) {

	/*assume that cpn is a connected graph*/

	for (auto it = group_vertices.begin(); it != group_vertices.end(); it++) {
		int g = *it;
		double p_g_not_coverred = 1;
		bool covered = false;

		for (auto it2 = cpn_vertices.begin(); it2 != cpn_vertices.end(); it2++) {
			int v = *it2;
			if (graph_v_of_v_idealID_contain_edge(group_graph, v, g)) {
				double p_g_v = graph_v_of_v_idealID_edge_weight(group_graph, v, g);
				p_g_not_coverred = p_g_not_coverred * (1 - p_g_v);
				if (1 - p_g_not_coverred >= b) {
					break;
				}
			}
		}
		if (1 - p_g_not_coverred < b) {
			return false;
		}
	}

	return true;

}
#pragma endregion there_is_a_feasible_PGST_in_this_cpn_graph_v_of_v_idealID

#pragma region
graph_hash_of_mixed_weighted make_solutree_feasible(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, graph_hash_of_mixed_weighted& input_solution_tree, double b,
	vector<vector<PLL_sorted_label>>& PLL_indexes, vector<int>& graph_id_2_PLL_id, vector<int>& PLL_id_2_graph_id) {

	graph_hash_of_mixed_weighted new_solu_tree = graph_hash_of_mixed_weighted_copy_graph(input_solution_tree);

	/*record uncoverred groups and uncoverred_probabilities*/
	unordered_map<int, double> uncoverred_groups; // <group_id, uncoverred_probability>
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int g = *it;
		double p_g_not_coverred = 1;
		bool covered = false;
		for (auto it2 = input_solution_tree.hash_of_vectors.begin(); it2 != input_solution_tree.hash_of_vectors.end(); it2++) {
			int v = it2->first;
			if (graph_v_of_v_idealID_contain_edge(group_graph, v, g)) {
				double p_g_v = graph_v_of_v_idealID_edge_weight(group_graph, v, g);
				p_g_not_coverred = p_g_not_coverred * (1 - p_g_v);
			}
		}
		double p_g_coverred = 1 - p_g_not_coverred;
		if (p_g_coverred <= b) {
			uncoverred_groups[g] = p_g_not_coverred;
		}
	}

	/*iteratively merge closest shortest paths*/
	while (uncoverred_groups.size() > 0) {

		/*record vertices that are connected with new_solu_tree*/
		vector<int> all_cpn_vertices = graph_v_of_v_idealID_breadth_first_search_a_set_of_vertices(input_graph, new_solu_tree.hash_of_vectors.begin()->first);

		/*find the clostest SP between new_solu_tree and nearby vertex in uncoverred_groups*/
		int inside_terminal = 0, outside_terminal = 0;
		double minimum_dis = INT_MAX;
		for (auto it2 = all_cpn_vertices.begin(); it2 != all_cpn_vertices.end(); it2++) {
			int outside_v = *it2;
			if (new_solu_tree.hash_of_vectors.count(outside_v) == 0) {
				bool outside_v_in_uncoverred_groups = false;
				for (auto it3 = uncoverred_groups.begin(); it3 != uncoverred_groups.end(); it3++) {
					int g = it3->first;
					if (graph_v_of_v_idealID_contain_edge(group_graph, outside_v, g) == true) {
						outside_v_in_uncoverred_groups = true;
						break;
					}
				}
				if (outside_v_in_uncoverred_groups) {
					for (auto it1 = new_solu_tree.hash_of_vectors.begin(); it1 != new_solu_tree.hash_of_vectors.end(); it1++) {
						int inside_v = it1->first;
						double dis = PLL_extract_distance_vectorFORMAT(PLL_indexes, graph_id_2_PLL_id[outside_v], graph_id_2_PLL_id[inside_v]);
						if (dis < minimum_dis) {
							inside_terminal = inside_v;
							outside_terminal = outside_v;
						}
					}
				}
			}
		}

		/*merge the clostest SP*/
		vector<int> newly_added_vertices;
		vector<pair<int, int>> SP = PLL_extract_shortest_path_vectorFORMAT(PLL_indexes, graph_id_2_PLL_id[inside_terminal], graph_id_2_PLL_id[outside_terminal]);
		for (auto it = SP.begin(); it != SP.end(); it++) {
			int v1 = PLL_id_2_graph_id[it->first], v2 = PLL_id_2_graph_id[it->second];
			if (new_solu_tree.hash_of_vectors.count(v1) == 0) {
				newly_added_vertices.push_back(v1);
			}
			if (new_solu_tree.hash_of_vectors.count(v2) == 0) {
				newly_added_vertices.push_back(v2);
			}
			double ec = graph_v_of_v_idealID_edge_weight(input_graph, v1, v2);
			graph_hash_of_mixed_weighted_add_edge(new_solu_tree, v1, v2, ec);
		}

		/*update uncoverred_groups*/
		for (auto it1 = newly_added_vertices.begin(); it1 != newly_added_vertices.end(); it1++) {
			int new_v = *it1;
			for (auto it2 = uncoverred_groups.begin(); it2 != uncoverred_groups.end(); it2++) {
				int g = it2->first;
				if (graph_v_of_v_idealID_contain_edge(group_graph, new_v, g) == true) {
					double ec = graph_v_of_v_idealID_edge_weight(group_graph, new_v, g);
					it2->second = it2->second * (1 - ec);
				}
			}
		}
		vector<int> newly_coverred_groups;
		for (auto it2 = uncoverred_groups.begin(); it2 != uncoverred_groups.end(); it2++) {
			if (1 - it2->second + 1e-8 >= b) { // 1e-8 is error bound
				newly_coverred_groups.push_back(it2->first);
			}
		}
		for (auto it1 = newly_coverred_groups.begin(); it1 != newly_coverred_groups.end(); it1++) {
			uncoverred_groups.erase(*it1);
		}


	}


	return new_solu_tree;

}
#pragma endregion make_solutree_feasible

#pragma region
bool this_is_an_essential_cover_of_g(graph_v_of_v_idealID& group_graph, vector<int>& vertex_set, int g, double b) {

	/*O(|vertex_set|) */

	/*check whether vertex_set covers g; O(|vertex_set|)*/
	double set_size = vertex_set.size();
	if (set_size == 0) {
		return false;
	}
	vector<double> vertex_probability(set_size, 0);
	queue<int> one_in_vertex_probability;
	double p_g_not_coverred = 1;
	for (int j = 0; j < set_size; j++) {
		if (graph_v_of_v_idealID_contain_edge(group_graph, vertex_set[j], g)) {
			vertex_probability[j] = graph_v_of_v_idealID_edge_weight(group_graph, vertex_set[j], g);
			if (vertex_probability[j] == 1) {
				one_in_vertex_probability.push(j);
			}
		}
		else {
			return false; // vertex_probability[j] = 0; the jth vertex is redundent for covering g
		}
		p_g_not_coverred = p_g_not_coverred * (1 - vertex_probability[j]);
	}
	/*every vertex_probability is positive below*/
	if (1 - p_g_not_coverred < b) {
		return false;
	}
	if (one_in_vertex_probability.size() > 1) {
		return false;
	}
	else if (one_in_vertex_probability.size() == 1) {
		if (set_size > 1) {
			return false;
		}
		else {
			return true;
		}
	}
	/*every vertex_probability is in (0,1) below*/

	/*check whether vertex_set is essential; O(|vertex_set|)*/
	for (int j = 0; j < set_size; j++) {
		double p_g_not_coverred_without_j = p_g_not_coverred / (1 - vertex_probability[j]);
		if (1 - p_g_not_coverred_without_j >= b) { // the ith vertex is redundent for covering g
			return false;
		}
	}
	return true;

}
#pragma endregion this_is_an_essential_cover_of_g




/*ENSteiner*/

#pragma region
graph_v_of_v_idealID transformation_to_STP_graph_v_of_v_idealID(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|V|+|E|+|T||V|)*/

	graph_v_of_v_idealID G_t(group_graph.size());
	int N = input_graph.size();

	/*initialization: set M to a large value*/
	double M = 1;
	for (int i = 0; i < N; i++) {
		for (int xx = input_graph[i].size() - 1; xx >= 0; xx--) {
			int j = input_graph[i][xx].first;
			if (i < j) { // edge (i,j)
				double c_ij = input_graph[i][xx].second;
				graph_v_of_v_idealID_add_edge(G_t, i, j, c_ij);
				M = M + c_ij;
			}
		}
	}

	/*add dummy vertices and edges*/
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group_vertex = *it;
		for (int xx = group_graph[group_vertex].size() - 1; xx >= 0; xx--) {
			int vertex = group_graph[group_vertex][xx].first;
			graph_v_of_v_idealID_add_edge(G_t, group_vertex, vertex, M); // add dummy edges
		}
	}

	return G_t;

}
#pragma endregion transformation_to_STP_graph_v_of_v_idealID

#pragma region
graph_hash_of_mixed_weighted shortest_path_heuristic_1980_graph_v_of_v_idealID(graph_v_of_v_idealID& G_t, std::unordered_set<int>& G_t_compulsory_vertices) {

	graph_hash_of_mixed_weighted solu_graph;

	/*start vertex/terminal and add it to solu_graph*/
	int start_vertex = *(G_t_compulsory_vertices.begin());
	graph_hash_of_mixed_weighted_add_vertex(solu_graph, start_vertex, 0);


	/*initialize unconnected terminals*/
	std::unordered_set<int> V2 = G_t_compulsory_vertices;
	V2.erase(start_vertex);


	/*find SPs from V2 to all the other vertices*/
	std::unordered_map<int, pair<vector<double>, vector<int>>> SPs; // <source,pair<distances,predecessors>>
	for (auto it1 = V2.begin(); it1 != V2.end(); it1++) {
		int source = *it1;
		vector<double> distances;
		vector<int> predecessors;
		graph_v_of_v_idealID_shortest_paths(G_t, source, distances, predecessors);
		SPs[source] = { distances ,predecessors };
	}


	/*concatinating paths; O(T^2 * V)*/
	while (V2.size() > 0) { // O(|T|)

		int path_V1_end, path_V2_end;
		double path_length = std::numeric_limits<double>::max();

		for (auto it0 = V2.begin(); it0 != V2.end(); it0++) { // O(|T|)
			int unconnected_terminal = *it0;
			for (auto it1 = solu_graph.hash_of_vectors.begin(); it1 != solu_graph.hash_of_vectors.end(); it1++) { // O(|V|)
				int connected_terminal = it1->first;
				double length = SPs[unconnected_terminal].first[connected_terminal];
				if (length < path_length) {
					path_V1_end = connected_terminal;
					path_V2_end = unconnected_terminal;
					path_length = length;
				}
			}
		}

		/*add path; O(|V|)*/
		int v = path_V1_end;
		while (v != path_V2_end) {
			int pre_v = SPs[path_V2_end].second[v];
			graph_hash_of_mixed_weighted_add_edge(solu_graph, v, pre_v, graph_v_of_v_idealID_edge_weight(G_t, v, pre_v));
			v = pre_v;
		}

		V2.erase(path_V2_end);

	}

	return solu_graph;

}
#pragma endregion shortest_path_heuristic_1980_graph_v_of_v_idealID

#pragma region
graph_hash_of_mixed_weighted ENSteiner(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph, std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|T||G_t_E|+|T||G_t_V|log|G_t_V|)*/

	/*transformation_to_STP; time complexity: O(|V|+|E|)*/
	graph_v_of_v_idealID G_t = transformation_to_STP_graph_v_of_v_idealID(input_graph, group_graph, cumpulsory_group_vertices);

	/*time complexity: O(|T||G_t_E|+|T||G_t_V|log|G_t_V|)*/
	graph_hash_of_mixed_weighted theta = shortest_path_heuristic_1980_graph_v_of_v_idealID(G_t, cumpulsory_group_vertices);

	/*remove_dummy_components; time complexity: O(|T|), as all terminals in leaves in LANCET solutions*/
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		graph_hash_of_mixed_weighted_remove_vertex(theta, *it);
	}

	return theta;

}
#pragma endregion ENSteiner


/*ImprovAPP*/

#pragma region
struct node_for_removeleaf_graph_v_of_v_idealID {
	int index;
	double priority_value; // distance
}; // define the node in the queue
bool operator<(node_for_removeleaf_graph_v_of_v_idealID const& x, node_for_removeleaf_graph_v_of_v_idealID const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the min heap
}

bool this_is_a_non_unique_group_leaf(graph_hash_of_mixed_weighted& theta_dash,
	std::unordered_map<int, std::unordered_set<int>>& groups_and_sets_of_vertices,
	std::unordered_map<int, std::unordered_set<int>>& vertices_and_sets_of_groups, int v) {

	/*time complexity O(|T|)*/

	if (graph_hash_of_mixed_weighted_adjacent_vertices_size(theta_dash, v) != 1) { // v is not a leaf
		return false;
	}

	for (auto it = vertices_and_sets_of_groups[v].begin(); it != vertices_and_sets_of_groups[v].end(); it++) {
		int group = *it;
		if (groups_and_sets_of_vertices[group].size() == 1) {
			return false;
		}
	}

	return true;

}

void remove_non_unique_group_leaves_graph_v_of_v_idealID(graph_hash_of_mixed_weighted& theta_dash, graph_v_of_v_idealID& group_graph, std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity O(|T||V|+|V|log|V|)*/

	/*time complexity O(|T||V|)*/
	std::unordered_map<int, std::unordered_set<int>> groups_and_sets_of_vertices, vertices_and_sets_of_groups;
	for (auto it = theta_dash.hash_of_vectors.begin(); it != theta_dash.hash_of_vectors.end(); it++) {
		int v = it->first;
		vertices_and_sets_of_groups[v] = {};
	}
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group = *it;
		groups_and_sets_of_vertices[group] = {};
	}
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int group = *it;

		for (int i = group_graph[group].size() - 1; i >= 0; i--) {
			int v = group_graph[group][i].first;
			if (theta_dash.hash_of_vectors.count(v) > 0) {
				groups_and_sets_of_vertices[group].insert(v);
				vertices_and_sets_of_groups[v].insert(group);
			}
		}
	}

	node_for_removeleaf_graph_v_of_v_idealID node;
	boost::heap::fibonacci_heap<node_for_removeleaf_graph_v_of_v_idealID> Q;

	/*push non_unique_group leaves into Q; time complexity O(|T||V|)*/
	for (auto it = theta_dash.hash_of_vectors.begin(); it != theta_dash.hash_of_vectors.end(); it++) {
		int leaf = (*it).first;

		auto search = theta_dash.hash_of_hashs.find(leaf);
		if (search != theta_dash.hash_of_hashs.end()) {
			if (search->second.size() == 1) {  // a leaf
				if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices, vertices_and_sets_of_groups, leaf)) {
					std::list<pair<int, double>> x = graph_hash_of_mixed_weighted_adjacent_vertices_and_weights(theta_dash, leaf);
					int adj_v = x.front().first;
					double ec = x.front().second;

					node.index = leaf;
					node.priority_value = ec;
					Q.push(node);
				}

			}
		}
		else {
			if (it->second.adj_vertices.size() == 1) {  // a leaf
				if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices, vertices_and_sets_of_groups, leaf)) {
					std::list<pair<int, double>> x = graph_hash_of_mixed_weighted_adjacent_vertices_and_weights(theta_dash, leaf);
					int adj_v = x.front().first;
					double ec = x.front().second;

					node.index = leaf;
					node.priority_value = ec;
					Q.push(node);
				}

			}
		}
	}

	/*time complexity O(|T||V|+|V|log|V|)*/
	while (Q.size() > 0) {

		int top_leaf = Q.top().index;
		Q.pop(); /*time complexity O(|V|log|V|)*/

		if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices, vertices_and_sets_of_groups, top_leaf)) {
			std::list<int> x = graph_hash_of_mixed_weighted_adjacent_vertices(theta_dash, top_leaf);
			int adj = x.front();
			graph_hash_of_mixed_weighted_remove_vertex(theta_dash, top_leaf); // remove this leaf

			/*update groups_and_sets_of_vertices, vertices_and_sets_of_groups*/
			/*time complexity O(|T|)*/
			for (auto it = vertices_and_sets_of_groups[top_leaf].begin();
				it != vertices_and_sets_of_groups[top_leaf].end(); it++) {
				int group = *it;
				groups_and_sets_of_vertices[group].erase(top_leaf);
			}
			vertices_and_sets_of_groups.erase(top_leaf);

			if (this_is_a_non_unique_group_leaf(theta_dash, groups_and_sets_of_vertices,
				vertices_and_sets_of_groups, adj)) { // adj is a new non_unique_group_leaf

				std::list<pair<int, double>> y = graph_hash_of_mixed_weighted_adjacent_vertices_and_weights(theta_dash, adj);

				int adj_adj = y.front().first;
				double ec = y.front().second;

				node.index = adj;
				node.priority_value = ec;
				Q.push(node);
			}

		}

	}


}
#pragma endregion remove_non_unique_group_leaves_graph_v_of_v_idealID

#pragma region
struct node_ImprovAPP_onlyec {
	int connected_v;
	int unconncected_g;
	double priority_value;
}; // define the node in the queue
bool operator<(node_ImprovAPP_onlyec const& x, node_ImprovAPP_onlyec const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the min heap
}
typedef typename boost::heap::fibonacci_heap<node_ImprovAPP_onlyec>::handle_type handle_node_ImprovAPP_onlyec;

void ImprovAPP_onlyec_iteration_process(int v, int g_min, std::unordered_set<int>& cumpulsory_group_vertices,
	graph_v_of_v_idealID& input_graph, graph_hash_of_mixed_weighted& theta_min, double& cost_theta_min, std::unordered_map<int, pair<vector<int>, vector<double>>>& SPs_to_groups) {

	/*time complexity: O(|T|(|V|+log|T|))*/

	/*initialization; time complexity: O(|T|)*/
	std::unordered_set<int> V_c, Gamma_uc = cumpulsory_group_vertices;
	V_c.insert(v);
	Gamma_uc.erase(g_min);
	graph_hash_of_mixed_weighted theta_v;
	node_ImprovAPP_onlyec node;
	boost::heap::fibonacci_heap<node_ImprovAPP_onlyec> Q;
	std::unordered_map<int, double> Q_keys;
	std::unordered_map<int, handle_node_ImprovAPP_onlyec> Q_handles;


	/*push LWPs into Q; time complexity: O(|T|)*/
	for (auto it1 = Gamma_uc.begin(); it1 != Gamma_uc.end(); it1++) {
		node.connected_v = v;
		node.unconncected_g = *it1;
		node.priority_value = SPs_to_groups[*it1].second[v];
		Q_keys[*it1] = node.priority_value;
		Q_handles[*it1] = Q.push(node);
	}


	/*time complexity: O(|T||V|+|T|log|T|)*/
	while (Gamma_uc.size() > 0) {

		int v_top = Q.top().connected_v, g_top = Q.top().unconncected_g;
		Q.pop(); // time complexity: O(log|T|)

		std::unordered_set<int> V_newc;

		/*merge LWP into theta_v; time complexity: O(|V|)*/
		graph_hash_of_mixed_weighted_add_vertex(theta_v, v_top, 0);
		int pre = SPs_to_groups[g_top].first[v_top]; // LWPs_to_groups[g_top].second is the predecessor index
		while (v_top != pre) {
			graph_hash_of_mixed_weighted_add_vertex(theta_v, pre, 0);
			V_newc.insert(pre); // pre is a newly connected vertex
			V_c.insert(pre); // pre is a newly connected vertex
			double ec = graph_v_of_v_idealID_edge_weight(input_graph, v_top, pre);
			graph_hash_of_mixed_weighted_add_edge(theta_v, v_top, pre, ec);
			v_top = pre;
			pre = SPs_to_groups[g_top].first[v_top];
		}
		Gamma_uc.erase(g_top); // update Gamma_uc


		/*update LWPs in Q; time complexity: O(|T||V|) throught the whole loop*/
		for (auto it = V_newc.begin(); it != V_newc.end(); it++) {
			int new_v = *it;
			for (auto it1 = Gamma_uc.begin(); it1 != Gamma_uc.end(); it1++) {
				int g = *it1;
				double new_v_to_g_weight = SPs_to_groups[g].second[new_v];
				if (new_v_to_g_weight < Q_keys[g]) {
					node.connected_v = new_v;
					node.unconncected_g = g;
					node.priority_value = new_v_to_g_weight;
					Q_keys[g] = new_v_to_g_weight;
					Q.update(Q_handles[g], node); // O(1), since it's decrease key
				}
			}
		}
	}

	/*update theta_min; time complexity: O(|V|)*/
	double cost_theta_v = graph_hash_of_mixed_weighted_sum_of_ec(theta_v);
	if (cost_theta_v < cost_theta_min) {
		cost_theta_min = cost_theta_v;
		theta_min = theta_v;
	}

}
#pragma endregion ImprovAPP_onlyec_iteration_process

#pragma region
graph_hash_of_mixed_weighted ImprovAPP_onlyec(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph, std::unordered_set<int>& cumpulsory_group_vertices) {

	/*time complexity: O(|T||E|+|T||V|log|V| + |g_min||T|(|V|+log|T|))*/

	int g_min = find_g_min_graph_v_of_v_idealID(group_graph, cumpulsory_group_vertices);
	//cout << "g_min=" << g_min << endl;

	/*time complexity: O(|T||E|+|T||V|log|V|)*/
	std::unordered_map<int, pair<vector<int>, vector<double>>> SPs_to_groups;
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int g_vertex = *it;
		if (g_vertex != g_min) {
			SPs_to_groups[g_vertex] = graph_v_of_v_idealID_PrunedDPPlusPlus_find_SPs_to_g(group_graph, input_graph, g_vertex);
		}
	}

	graph_hash_of_mixed_weighted theta_min;
	double cost_theta_min = INT_MAX;
	/*time complexity: O(|g_min||T|(|V|+log|T|))*/
	for (int i = group_graph[g_min].size() - 1; i >= 0; i--) {
		int v = group_graph[g_min][i].first; // vertex is in group g_min
		ImprovAPP_onlyec_iteration_process(v, g_min, cumpulsory_group_vertices, input_graph, theta_min, cost_theta_min, SPs_to_groups);
	}

	/*update MST; time complexity: O(|E|+|V|log|V|)*/
	unordered_set<int> G_min;
	for (auto it = theta_min.hash_of_vectors.begin(); it != theta_min.hash_of_vectors.end(); it++) {
		G_min.insert(it->first);
	}
	theta_min = graph_v_of_v_idealID_MST_postprocessing(input_graph, G_min);

	/*time complexity O(|T||V|+|V|log|V|)*/
	remove_non_unique_group_leaves_graph_v_of_v_idealID(theta_min, group_graph, cumpulsory_group_vertices);

	/*time complexity: O(|V|)*/
	return theta_min;

}
#pragma endregion ImprovAPP_onlyec




/*proposed algorithms*/

#pragma region
std::vector<vector<int>> all_essential_covers_of_a_group_graph_v_of_v_idealID(graph_v_of_v_idealID& group_graph, int g, double b) {

	std::vector<vector<int>> all_essential_covers;

	double p_g_min = graph_v_of_v_idealID_smallest_adj_edge_weight(group_graph, g);
	int xi_g = (log(1 - b) / log(1 - p_g_min)) + 1; // smallest int value not smaller than log; C++ Casting to an int truncates the value
	std::vector<int> g_vertices;
	for (int i = group_graph[g].size() - 1; i >= 0; i--) {
		g_vertices.push_back(group_graph[g][i].first);
	}
	if (xi_g > g_vertices.size()) {
		xi_g = g_vertices.size(); // xi_g should not be larger than g_vertices.size() is the following permutation
	}

	for (int v_set_size = 1; v_set_size <= xi_g; v_set_size++) {
		//print_vector_v1(g_vertices);
		//cout << "g_vertices.size(): " << g_vertices.size() << " v_set_size: " << v_set_size << endl;
		std::vector<vector<int>> g_permutation_elements = for_each_reversible_circular_permutation
		(g_vertices.begin(), g_vertices.begin() + v_set_size, g_vertices.end(), permutations_ys_function(g_vertices.size())).GetVect();
		int g_permutation_elements_size = g_permutation_elements.size();
		//cout << "g_permutation_elements_size:" << g_permutation_elements_size << endl; // 50^5=312500000, this is not scalable at all!
		if (g_permutation_elements_size > 1e7) {
			cout << "g_permutation_elements_size is too large!!" << endl;
			//exit(1);
		}
		for (int i = 0; i < g_permutation_elements_size; i++) {
			if (this_is_an_essential_cover_of_g(group_graph, g_permutation_elements[i], g, b)) {
				all_essential_covers.push_back(g_permutation_elements[i]);
				//cout << "all_essential_covers.size():" << all_essential_covers.size() << endl;
			}
		}
	}

	return all_essential_covers;

}
#pragma endregion all_essential_covers_of_a_group_graph_v_of_v_idealID

#pragma region
graph_hash_of_mixed_weighted algo1_DUAL_graph_v_of_v_idealID(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double b, double tau) {

	graph_hash_of_mixed_weighted solu_tree;
	double solu_tree_weight = INT_MAX;

	int Phi_min_g = 0, Phi_min_size = INT_MAX;
	std::unordered_map<int, std::vector<vector<int>>> Phi; // all essential covers of all g
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		Phi[*it] = all_essential_covers_of_a_group_graph_v_of_v_idealID(group_graph, *it, b);
		//cout << "Phi[*it].size(): " << Phi[*it].size() << endl;
		if (Phi_min_size > Phi[*it].size()) {
			Phi_min_g = *it;
		}
	}

	int N = input_graph.size();
	graph_v_of_v_idealID group_graph_base(N);

	//cout << "Phi_min_g: " << Phi_min_g << endl;
	auto it_begin = Phi[Phi_min_g].begin(), it_end = Phi[Phi_min_g].end();
	for (; it_begin != it_end; it_begin++) {
		vector<int> V_dash = *it_begin;
		graph_hash_of_mixed_weighted Theta_V_dash;

		if (cumpulsory_group_vertices.size() == 1) {

			/*produce each vertex in V_dash as a new singular group*/
			std::unordered_set<int> new_cumpulsory_group_vertices;
			for (int i = 0; i < V_dash.size(); i++) {
				int new_v_id = group_graph_base.size();
				group_graph_base.resize(new_v_id + 1);
				graph_v_of_v_idealID_add_edge(group_graph_base, V_dash[i], new_v_id, 0);
				new_cumpulsory_group_vertices.insert(new_v_id);
			}

			Theta_V_dash = graph_v_of_v_idealID_PrunedDPPlusPlus(input_graph, group_graph_base, new_cumpulsory_group_vertices, tau);

			group_graph_base.resize(N);
			for (int i = 0; i < V_dash.size(); i++) {
				graph_hash_of_mixed_weighted_binary_operations_erase(group_graph_base[V_dash[i]], N + i);
			}

		}
		else {

			graph_hash_of_mixed_weighted G_dash;

			for (auto it1 = cumpulsory_group_vertices.begin(); it1 != cumpulsory_group_vertices.end(); it1++) {
				if (*it1 != Phi_min_g) {
					int g = *it1;
					graph_hash_of_mixed_weighted Theta_ST_V_dash_Phi_g;
					double Theta_ST_V_dash_Phi_g_weight = INT_MAX;

					auto it_begin2 = Phi[g].begin(), it_end2 = Phi[g].end();
					for (; it_begin2 != it_end2; it_begin2++) {
						vector<int> V_j = *it_begin2;
						vector<int> V_combine;
						V_combine.insert(V_combine.end(), V_dash.begin(), V_dash.end());
						V_combine.insert(V_combine.end(), V_j.begin(), V_j.end());

						/*produce each vertex in V_dash as a new singular group*/
						std::unordered_set<int> new_cumpulsory_group_vertices;
						for (int i = 0; i < V_combine.size(); i++) {
							int new_v_id = group_graph_base.size();
							group_graph_base.resize(new_v_id + 1);
							graph_v_of_v_idealID_add_edge(group_graph_base, V_combine[i], new_v_id, 0);
							new_cumpulsory_group_vertices.insert(new_v_id);
						}
						//graph_v_of_v_idealID_print(input_graph);
						//print_unordered_set_v1(new_cumpulsory_group_vertices);
						//cout << "group_graph_base: " << endl;
						//graph_v_of_v_idealID_print(group_graph_base);

						graph_hash_of_mixed_weighted Theta_V_dash_V_j = graph_v_of_v_idealID_PrunedDPPlusPlus(input_graph, group_graph_base, new_cumpulsory_group_vertices, tau);

						group_graph_base.resize(N);
						for (int i = 0; i < V_combine.size(); i++) {
							graph_hash_of_mixed_weighted_binary_operations_erase(group_graph_base[V_combine[i]], N + i);
						}

						double Theta_V_dash_V_j_weight = graph_hash_of_mixed_weighted_sum_of_ec(Theta_V_dash_V_j);
						if (Theta_V_dash_V_j_weight < Theta_ST_V_dash_Phi_g_weight) {
							Theta_ST_V_dash_Phi_g_weight = Theta_V_dash_V_j_weight;
							Theta_ST_V_dash_Phi_g = Theta_V_dash_V_j;
						}
					}

					graph_hash_of_mixed_weighted_merge_g2_into_g1(G_dash, Theta_ST_V_dash_Phi_g);
				}
			}

			std::unordered_set<int> hash_of_v;
			for (auto it = G_dash.hash_of_vectors.begin(); it != G_dash.hash_of_vectors.end(); it++) {
				hash_of_v.insert(it->first);
			}
			Theta_V_dash = graph_v_of_v_idealID_MST_postprocessing(input_graph, hash_of_v);
		}

		double Theta_V_dash_weight = graph_hash_of_mixed_weighted_sum_of_ec(Theta_V_dash);
		if (Theta_V_dash_weight < solu_tree_weight) {
			solu_tree_weight = Theta_V_dash_weight;
			solu_tree = Theta_V_dash;
		}

	}

	return solu_tree;
}
#pragma endregion algo1_DUAL_graph_v_of_v_idealID

#pragma region
void add_a_new_vertex_update_not_covered_groups_graph_v_of_v_idealID(std::unordered_map<int, double>& not_covered_groups, int new_v,
	graph_v_of_v_idealID& group_graph, double b, graph_v_of_v_idealID& new_group_graph, std::unordered_set<int>& new_cumpulsory_group_vertices) {

	vector<int> newly_coverred_groups;

	/*O(T)*/

	for (auto it = not_covered_groups.begin(); it != not_covered_groups.end(); it++) {

		graph_v_of_v_idealID_remove_edge(new_group_graph, it->first, new_v); // newly added vertices are not in new groups

		if (graph_v_of_v_idealID_contain_edge(group_graph, it->first, new_v)) {
			double p = graph_v_of_v_idealID_edge_weight(group_graph, it->first, new_v);
			it->second = it->second * (1 - p); // update not coverred probabilities
			if (1 - it->second >= b) {
				newly_coverred_groups.push_back(it->first); // not_covered_groups do not contain singel_v_group, so singel_v_group will not be removed from new_cumpulsory_group_vertices
			}
		}

	}

	for (int i = newly_coverred_groups.size() - 1; i >= 0; i--) {
		not_covered_groups.erase(newly_coverred_groups[i]);
		new_cumpulsory_group_vertices.erase(newly_coverred_groups[i]);
	}
}

graph_hash_of_mixed_weighted algo2_GRETREE_graph_v_of_v_idealID(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double b, double tau) {

	graph_hash_of_mixed_weighted solu_tree;
	double solu_tree_weight = INT_MAX;

	int g_min = 0, g_min_size = INT_MAX;
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int degree = group_graph[*it].size();
		if (g_min_size > degree) {
			g_min_size = degree;
			g_min = *it;
		}
	}

	for (int i = group_graph[g_min].size() - 1; i >= 0; i--) {
		int v = group_graph[g_min][i].first;

		graph_hash_of_mixed_weighted G_dash;
		std::unordered_set<int> G_dash_V_set;
		graph_hash_of_mixed_weighted_add_vertex(G_dash, v, 0);
		G_dash_V_set.insert(v);

		/*
		produce new_group_graph;
		it is faster to produce new_group_graph in the loop; experiments show that it is much slower to produce new_group_graph before the loop,
		and record and then restore removed edges in new_group_graph in each loop
		*/
		graph_v_of_v_idealID new_group_graph = group_graph;
		int old_group_graph_size = group_graph.size();
		new_group_graph.resize(old_group_graph_size + 1);
		graph_v_of_v_idealID_add_edge(new_group_graph, old_group_graph_size, v, 1); // old_group_graph_size is a new singular group contains v

		/*produce not_covered_groups*/
		std::unordered_map<int, double> not_covered_groups; // double value is not_coverred probability
		for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
			not_covered_groups[*it] = 1;
		}

		/*produce new new_cumpulsory_group_vertices*/
		std::unordered_set<int> new_cumpulsory_group_vertices = cumpulsory_group_vertices;
		new_cumpulsory_group_vertices.insert(old_group_graph_size); // add a new singular group contains v

		/*update new_group_graph for the single vertex v*/
		add_a_new_vertex_update_not_covered_groups_graph_v_of_v_idealID(not_covered_groups, v, group_graph, b, new_group_graph, new_cumpulsory_group_vertices);

		/*iteratively concatinating*/
		while (not_covered_groups.size() > 0) {

			graph_hash_of_mixed_weighted Theta_dash = graph_v_of_v_idealID_PrunedDPPlusPlus(input_graph, new_group_graph, new_cumpulsory_group_vertices, tau);

			for (auto it = Theta_dash.hash_of_vectors.begin(); it != Theta_dash.hash_of_vectors.end(); it++) {
				if (G_dash.hash_of_vectors.count(it->first) == 0) {
					int new_v = it->first;
					G_dash_V_set.insert(new_v);
					add_a_new_vertex_update_not_covered_groups_graph_v_of_v_idealID(not_covered_groups, new_v, group_graph, b, new_group_graph, new_cumpulsory_group_vertices);
				}
			}

			graph_hash_of_mixed_weighted_merge_g2_into_g1(G_dash, Theta_dash);
		}

		/*MST_postprocessing*/
		graph_hash_of_mixed_weighted Theta_v = graph_v_of_v_idealID_MST_postprocessing(input_graph, G_dash_V_set);

		/*update solu_tree*/
		double Theta_v_weight = graph_hash_of_mixed_weighted_sum_of_ec(Theta_v);
		if (Theta_v_weight < solu_tree_weight) {
			solu_tree_weight = Theta_v_weight;
			solu_tree = Theta_v;
		}
	}

	return solu_tree;
}
#pragma endregion algo2_GRETREE_graph_v_of_v_idealID

#pragma region
struct remove_redundent_leaves_max_heap_node {
	int v;
	double priority_value;
};
bool operator<(remove_redundent_leaves_max_heap_node const& x, remove_redundent_leaves_max_heap_node const& y) {
	return x.priority_value < y.priority_value; // < is the max-heap; > is the min heap;
}
void remove_redundent_leaves_graph_v_of_v_idealID(graph_hash_of_mixed_weighted& solu_tree, graph_v_of_v_idealID& group_graph, std::unordered_set<int>& cumpulsory_group_vertices, double b) {

	boost::heap::fibonacci_heap<remove_redundent_leaves_max_heap_node> Q_max;
	remove_redundent_leaves_max_heap_node node;
	for (auto it = solu_tree.hash_of_vectors.begin(); it != solu_tree.hash_of_vectors.end(); it++) {
		if (solu_tree.degree(it->first) == 1) { // leaf
			vector<pair<int, double>> adj_v_ec = solu_tree.adj_v_and_ec(it->first);
			node.v = it->first;
			node.priority_value = adj_v_ec.begin()->second;
			Q_max.push(node);
		}
	}

	while (Q_max.size() > 0) {
		node = Q_max.top();
		Q_max.pop();

		bool v_can_be_removed = true;
		for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
			double p_g_not_coverred = 1;
			for (auto it2 = solu_tree.hash_of_vectors.begin(); it2 != solu_tree.hash_of_vectors.end(); it2++) {
				if (it2->first != node.v) {
					if (graph_v_of_v_idealID_contain_edge(group_graph, it2->first, *it)) {
						double p_g_v = graph_v_of_v_idealID_edge_weight(group_graph, it2->first, *it);
						p_g_not_coverred = p_g_not_coverred * (1 - p_g_v);
					}
				}
			}
			if (1 - p_g_not_coverred < b) {
				v_can_be_removed = false;
				break;
			}
		}

		if (v_can_be_removed) {
			std::vector<int> adj_v = solu_tree.adj_v(node.v);
			graph_hash_of_mixed_weighted_remove_vertex(solu_tree, node.v);
			if (solu_tree.degree(*adj_v.begin()) == 1) { // leaf
				vector<pair<int, double>> adj_v_ec = solu_tree.adj_v_and_ec(*adj_v.begin());
				node.v = *adj_v.begin();
				node.priority_value = adj_v_ec.begin()->second;
				Q_max.push(node);
			}
		}
	}
}
#pragma endregion remove_redundent_leaves_graph_v_of_v_idealID

#pragma region
struct algo3_GREPATH_min_heap_node {
	int u;
	double priority_value;
};
bool operator<(algo3_GREPATH_min_heap_node const& x, algo3_GREPATH_min_heap_node const& y) {
	return x.priority_value > y.priority_value; // < is the max-heap; > is the min heap;
}

void add_a_new_vertex_update_not_cover_probabilities_graph_v_of_v_idealID(std::unordered_map<int, double>& not_cover_probabilities, int new_v, graph_v_of_v_idealID& group_graph, double b) {

	for (auto it = not_cover_probabilities.begin(); it != not_cover_probabilities.end(); it++) {
		if (graph_v_of_v_idealID_contain_edge(group_graph, it->first, new_v)) {
			double p = graph_v_of_v_idealID_edge_weight(group_graph, it->first, new_v);
			it->second = it->second * (1 - p);
		}
	}
}

graph_hash_of_mixed_weighted algo3_GREPATH_graph_v_of_v_idealID(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& group_graph,
	std::unordered_set<int>& cumpulsory_group_vertices, double b, double tau, vector<vector<PLL_sorted_label>>& PLL_indexes, vector<int>& graph_id_2_PLL_id, vector<int>& PLL_id_2_graph_id) {

	graph_hash_of_mixed_weighted solu_tree;
	double solu_tree_weight = INT_MAX;

	int g_min = 0, g_min_size = INT_MAX;
	for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
		int degree = group_graph[*it].size();
		if (g_min_size > degree) {
			g_min_size = degree;
			g_min = *it;
		}
	}

	for (int ii = group_graph[g_min].size() - 1; ii >= 0; ii--) {
		int v = group_graph[g_min][ii].first;
		int v_PLL_id = graph_id_2_PLL_id[v];

		/*initialize heaps*/
		std::unordered_map<int, boost::heap::fibonacci_heap<algo3_GREPATH_min_heap_node>> heaps;
		algo3_GREPATH_min_heap_node node;
		for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
			boost::heap::fibonacci_heap<algo3_GREPATH_min_heap_node> Q;
			for (int j = group_graph[*it].size() - 1; j >= 0; j--) {
				double d_vu = PLL_extract_distance_vectorFORMAT(PLL_indexes, v_PLL_id, graph_id_2_PLL_id[group_graph[*it][j].first]);
				node.u = group_graph[*it][j].first;
				node.priority_value = d_vu;
				Q.push(node);
			}
			heaps[*it] = Q;
		}

		graph_hash_of_mixed_weighted Theta_v;
		std::unordered_map<int, double> not_cover_probabilities; // double value is not_coverred probability
		for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
			not_cover_probabilities[*it] = 1;
		}

		/*add v to Theta_v*/
		add_a_new_vertex_update_not_cover_probabilities_graph_v_of_v_idealID(not_cover_probabilities, v, group_graph, b);
		graph_hash_of_mixed_weighted_add_vertex(Theta_v, v, 0);

		for (auto it = cumpulsory_group_vertices.begin(); it != cumpulsory_group_vertices.end(); it++) {
			while (1 - not_cover_probabilities[*it] + 1e-8 < b) {
				algo3_GREPATH_min_heap_node top_node = heaps[*it].top();
				heaps[*it].pop();
				vector<pair<int, int>> edges = PLL_extract_shortest_path_vectorFORMAT(PLL_indexes, v_PLL_id, graph_id_2_PLL_id[top_node.u]);
				for (int j = edges.size() - 1; j >= 0; j--) {
					int v1 = PLL_id_2_graph_id[edges[j].first], v2 = PLL_id_2_graph_id[edges[j].second];
					if (Theta_v.hash_of_vectors.count(v1) == 0) {
						add_a_new_vertex_update_not_cover_probabilities_graph_v_of_v_idealID(not_cover_probabilities, v1, group_graph, b);
					}
					if (Theta_v.hash_of_vectors.count(v2) == 0) {
						add_a_new_vertex_update_not_cover_probabilities_graph_v_of_v_idealID(not_cover_probabilities, v2, group_graph, b);
					}
					double ec = graph_v_of_v_idealID_edge_weight(input_graph, v1, v2);
					graph_hash_of_mixed_weighted_add_edge(Theta_v, v1, v2, ec);
				}
			}
		}

		double Theta_v_weight = graph_hash_of_mixed_weighted_sum_of_ec(Theta_v);
		if (Theta_v_weight < solu_tree_weight) {
			solu_tree_weight = Theta_v_weight;
			solu_tree = Theta_v;
		}
	}

	std::unordered_set<int> hash_of_v;
	for (auto it = solu_tree.hash_of_vectors.begin(); it != solu_tree.hash_of_vectors.end(); it++) {
		hash_of_v.insert(it->first);
	}
	solu_tree = graph_v_of_v_idealID_MST_postprocessing(input_graph, hash_of_v);

	//remove_redundent_leaves_graph_v_of_v_idealID(solu_tree, group_graph, cumpulsory_group_vertices, b);

	return solu_tree;
}
#pragma endregion algo3_GREPATH_graph_v_of_v_idealID




/*experiments*/

/*read raw data*/

#pragma region 
void read_dblp_v12(graph_hash_of_mixed_weighted& read_graph, graph_hash_of_mixed_weighted& read_group_graph, std::unordered_set<int>& group_vertices, string dblp_size) {

	/* dblp_size is either 1248k or 2498k */

	/*this function can clear existing graph data*/
	read_graph.hash_of_vectors.clear();
	read_graph.hash_of_hashs.clear();
	read_group_graph.hash_of_vectors.clear();
	read_group_graph.hash_of_hashs.clear();
	group_vertices.clear();

	int group_ID_start = 1e7;

	string file_name = "DBLP_" + dblp_size + "_with_fosweights//dblp_v12_authors_" + dblp_size + ".txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "<&>"); // parse line_content

				int author_id = stoi(Parsed_content[0]);
				double citation_num = stod(Parsed_content[3]);
				double paper_num = stod(Parsed_content[4]);
				graph_hash_of_mixed_weighted_add_vertex(read_graph, author_id, 0); // add vertex to read_graph
				graph_hash_of_mixed_weighted_add_vertex(read_group_graph, author_id, 0); // add vertex to read_group_graph

				std::vector<string> Parsed_fields = parse_substring_between_pairs_of_delimiters(Parsed_content[2], "<", ">"); // parse line_content
				for (int i = 0; i < Parsed_fields.size(); i++) {
					std::vector<string> xx = parse_string(Parsed_fields[i], ",");
					if (string_is_number(xx[0]) && string_is_number(xx[1])) {
						int group_id = group_ID_start + stoi(xx[0]);
						group_vertices.insert(group_id);
						graph_hash_of_mixed_weighted_add_edge(read_group_graph, author_id, group_id, stod(xx[1])); // add weighted edge (author-keyword weight) to read_group_graph
					}
				}
			}
			count++;
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	file_name = "DBLP_" + dblp_size + "_with_fosweights//dblp_v12_linkes_" + dblp_size + ".txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "<&>"); // parse line_content
				int id1 = stoi(Parsed_content[0]);
				int id2 = stoi(Parsed_content[1]);
				graph_hash_of_mixed_weighted_add_edge(read_graph, id1, id2, 1); // add edge to read_graph
			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	cout << "num_vertices(read_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "num_edges(read_graph): " << graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;
	cout << "num_vertices(read_group_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_group_graph) << endl;
	cout << "num_edges(read_group_graph): " << graph_hash_of_mixed_weighted_num_edges(read_group_graph) << endl;
	cout << "group_vertices.size(): " << group_vertices.size() << endl;
}
#pragma endregion read_dblp_v12

#pragma region 
void read_Movielens_25m(graph_hash_of_mixed_weighted& read_graph, graph_hash_of_mixed_weighted& read_group_graph,
	std::unordered_map<int, string>& movie_names, std::unordered_map<int, string>& genres_names, std::unordered_set<int>& group_vertices) {

	/*this function can clear existing graph data*/
	read_graph.hash_of_vectors.clear();
	read_graph.hash_of_hashs.clear();
	read_group_graph.hash_of_vectors.clear();
	read_group_graph.hash_of_hashs.clear();
	movie_names.clear();
	genres_names.clear();
	group_vertices.clear();

	int group_ID_start = 1e7;

	std::unordered_map<std::string, int> genres_ids;

	string file_name = "MovieLens_25M//MovieLens_25M_movie_info.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, ":::"); // parse line_content

				//print_a_sequence_of_elements_v1(Parsed_content);

				int movie_id = stoi(Parsed_content[0]);
				string movie_name = Parsed_content[1];
				movie_names[movie_id] = movie_name;

				//cout << movie_name << endl;

				double avg_star = stod(Parsed_content[2]);

				graph_hash_of_mixed_weighted_add_vertex(read_graph, movie_id, avg_star); // add vertex to read_graph, with weights
				graph_hash_of_mixed_weighted_add_vertex(read_group_graph, movie_id, 0); // add vertex to read_group_graph; read_group_graph contains all movies

				std::vector<string> genres = parse_string(Parsed_content[3], "|");

				//print_a_sequence_of_elements_v1(genres);

				for (int i = 0; i < genres.size(); i++) {
					int genre_id = stoi(parse_string(genres[i], "_")[0]);
					if (genre_id != 19) { // != "(no genres listed)"
						genre_id = genre_id + group_ID_start;
						genres_names[genre_id] = parse_string(genres[i], "_")[1];
						group_vertices.insert(genre_id);
						graph_hash_of_mixed_weighted_add_edge(read_group_graph, movie_id, genre_id, avg_star); // add edge to read_group_graph (weight of movie-genre pair is avg rating of movie)
					}
				}
			}
			count++;
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}

	//print_unordered_map_int_string(genres_names);

	file_name = "MovieLens_25M//MovieLens_25M_movie_links.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, ":::"); // parse line_content
				int movie_id1 = stoi(Parsed_content[0]);
				int movie_id2 = stoi(Parsed_content[1]);
				int Number_of_common_5_star_raters = stoi(Parsed_content[2]);
				double ec = (double)1 / Number_of_common_5_star_raters; // how to define edge costs
				graph_hash_of_mixed_weighted_add_edge(read_graph, movie_id1, movie_id2, 1); // add edge to read_graph
			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	cout << "num_vertices(read_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "num_edges(read_graph): " << graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;
	cout << "num_vertices(read_group_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_group_graph) << endl;
	cout << "num_edges(read_group_graph): " << graph_hash_of_mixed_weighted_num_edges(read_group_graph) << endl;
	cout << "group_vertices.size(): " << group_vertices.size() << endl;


	//print_unordered_map_int_string(genres_names);


}
#pragma endregion read_Movielens_25m 

#pragma region 
void read_amazon(graph_hash_of_mixed_weighted& read_graph, graph_hash_of_mixed_weighted& read_group_graph, std::unordered_set<int>& group_vertices) {

	/*this function can clear existing graph data*/
	read_graph.hash_of_vectors.clear();
	read_graph.hash_of_hashs.clear();
	read_group_graph.hash_of_vectors.clear();
	read_group_graph.hash_of_hashs.clear();
	group_vertices.clear();

	string file_name = "amazon//amazon_items.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {
				int v = stoi(parse_substring_between_two_unique_delimiters(line_content, "<itemid>", "<itemid/>")); // parse line_content
				double avg_rating = stod(parse_substring_between_two_unique_delimiters(line_content, "<avg_rating>", "<avg_rating/>"));

				graph_hash_of_mixed_weighted_add_vertex(read_graph, v, 0); // add vertex to read_graph
				graph_hash_of_mixed_weighted_add_vertex(read_group_graph, v, 0); // add vertex to read_group_graph

				string keywords = parse_substring_between_two_unique_delimiters(line_content, "<keywords>", "<keywords/>");
				if (keywords != "") {
					std::vector<string> Parsed_keywords = parse_string(keywords, ",");
					for (auto it = Parsed_keywords.begin(); it != Parsed_keywords.end(); it++) {
						group_vertices.insert(stoi(*it));
						graph_hash_of_mixed_weighted_add_edge(read_group_graph, v, stoi(*it), avg_rating); // add weighted edge to read_group_graph  (weight of item-keyword pair is avg rating of item)
					}
				}
			}
			count++;
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	file_name = "amazon//amazon_items_links.txt";
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, ","); // parse line_content
				int id1 = stoi(Parsed_content[0]);
				int id2 = stoi(Parsed_content[1]);
				if (read_graph.hash_of_vectors.count(id1) == 0) {
					cout << "here: " << id1 << endl;
					getchar();
				}
				if (read_graph.hash_of_vectors.count(id2) == 0) {
					cout << "here: " << id2 << endl;
					getchar();
				}
				graph_hash_of_mixed_weighted_add_edge(read_graph, id1, id2, 1); // add edge to read_graph
			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}


	cout << "num_vertices(read_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_graph) << endl;
	cout << "num_edges(read_graph): " << graph_hash_of_mixed_weighted_num_edges(read_graph) << endl;
	cout << "num_vertices(read_group_graph): " << graph_hash_of_mixed_weighted_num_vertices(read_group_graph) << endl;
	cout << "num_edges(read_group_graph): " << graph_hash_of_mixed_weighted_num_edges(read_group_graph) << endl;
	cout << "group_vertices.size(): " << group_vertices.size() << endl;
}
#pragma endregion read_amazon

/*produce_small_graphs_for_experiments*/

#pragma region
void produce_small_dblp_v12() {

	int new_V = 2497782 / 2;

	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open("dblp_v12_authors_" + to_string((int)(new_V / 1e3)) + "k.txt");
	outputFile << "Author_ID<&>Author_name<&>Fields_of_study_IDs_and_Weights<&>Citation_num<&>Paper_num(total_author_number:" << new_V << ")" << endl;


	string file_name = "DBLP_2498k_with_fosweights//dblp_v12_authors.txt";
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "<&>"); // parse line_content

				int author_id = stoi(Parsed_content[0]);
				if (author_id < new_V) {
					outputFile << line_content << endl;
				}
			}
			count++;
		}
		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}
	outputFile.close();



	file_name = "DBLP_2498k_with_fosweights//dblp_v12_linkes.txt";
	outputFile.open("dblp_v12_linkes_" + to_string((int)(new_V / 1e3)) + "k.txt");
	outputFile << "Author_ID1<&>Author_ID2" << endl;
	ifstream myfile2(file_name); // open the file
	if (myfile2.is_open()) // if the file is opened successfully
	{
		int count = 0;
		while (getline(myfile2, line_content)) // read file line by line
		{
			if (count > 0) {
				std::vector<string> Parsed_content = parse_string(line_content, "<&>"); // parse line_content
				int id1 = stoi(Parsed_content[0]);
				int id2 = stoi(Parsed_content[1]);
				if (id1 < new_V && id2 < new_V) {
					outputFile << line_content << endl;
				}
			}
			count++;
		}
		myfile2.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}
	outputFile.close();
}
#pragma endregion produce_small_dblp_v12

#pragma region
void produce_small_graphs_for_experiments_element(string data_name, string save_read_graph_name, string save_read_group_graph_name, int V, bool one_edge_weight) {

	/*read data*/
	auto time1 = std::chrono::high_resolution_clock::now();

	std::unordered_set<int> old_group_vertices;
	graph_hash_of_mixed_weighted old_read_graph, old_read_group_graph;
	if (data_name == "dblp") {
		if (one_edge_weight) {
			read_dblp_v12(old_read_graph, old_read_group_graph, old_group_vertices, "2498k");
		}
		else {
			read_dblp_v12(old_read_graph, old_read_group_graph, old_group_vertices, "1248k");
		}
	}
	else if (data_name == "movie") {
		std::unordered_map<int, string> movie_names, genres_names;
		read_Movielens_25m(old_read_graph, old_read_group_graph, movie_names, genres_names, old_group_vertices);
	}
	else if (data_name == "amazon") {
		read_amazon(old_read_graph, old_read_group_graph, old_group_vertices);
	}

	if (one_edge_weight == false) {
		/*no ec normalization due to 0 ec not allowed*/
		auto time2 = std::chrono::high_resolution_clock::now();
		double runningtime1 = std::chrono::duration_cast<std::chrono::nanoseconds>(time2 - time1).count() / 1e9; // s
		cout << "runningtime1: " << runningtime1 << "s" << endl;
		graph_hash_of_mixed_weighted_ec_update_pairwise_jaccard_distance_fast(old_read_graph, old_read_graph.hash_of_vectors.size() + 1); // edge weight is jaccard_distance
		auto time3 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(time3 - time2).count() / 1e9; // s
		cout << "runningtime2: " << runningtime2 << "s" << endl;
	}

	if (V < old_read_graph.hash_of_vectors.size()) {

		/*make old_read_graph and old_read_group_graph smaller*/

		unordered_set<int> selected_vertices = graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn(old_read_graph, V);
		old_read_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices(old_read_graph, selected_vertices);

		std::unordered_set<int> small_read_graph_group_vertices;
		for (auto it = old_read_graph.hash_of_vectors.begin(); it != old_read_graph.hash_of_vectors.end(); it++) {
			int v = it->first;
			auto search = old_read_group_graph.hash_of_hashs.find(v);
			if (search != old_read_group_graph.hash_of_hashs.end()) {
				for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
					small_read_graph_group_vertices.insert(it2->first);
				}
			}
			else {
				auto search3 = old_read_group_graph.hash_of_vectors.find(v);
				for (auto it2 = search3->second.adj_vertices.begin(); it2 != search3->second.adj_vertices.end(); it2++) {
					small_read_graph_group_vertices.insert(it2->first);
				}
			}
		}

		vector<int> removed_vertices_from_old_read_group_graph;
		for (auto it = old_read_group_graph.hash_of_vectors.begin(); it != old_read_group_graph.hash_of_vectors.end(); it++) {
			int v = it->first;
			if (old_read_graph.hash_of_vectors.count(v) == 0 && small_read_graph_group_vertices.count(v) == 0) {
				removed_vertices_from_old_read_group_graph.push_back(v);
			}
		}
		for (int i = removed_vertices_from_old_read_group_graph.size() - 1; i >= 0; i--) {
			graph_hash_of_mixed_weighted_remove_vertex(old_read_group_graph, removed_vertices_from_old_read_group_graph[i]);
		}

	}

	graph_hash_of_mixed_weighted_binary_save(old_read_graph, save_read_graph_name);
	graph_hash_of_mixed_weighted_binary_save(old_read_group_graph, save_read_group_graph_name);

	/*check results*/
	graph_hash_of_mixed_weighted read_graph = graph_hash_of_mixed_weighted_binary_read(save_read_graph_name);
	graph_hash_of_mixed_weighted read_group_graph = graph_hash_of_mixed_weighted_binary_read(save_read_group_graph_name);

	if (graph_hash_of_mixed_weighted_graph1_is_graph2(read_graph, old_read_graph) == false) {
		cout << "graph_hash_of_mixed_weighted_graph1_is_graph2(read_graph, old_read_graph) == false!" << endl;
		exit(1);
	}
	if (graph_hash_of_mixed_weighted_graph1_is_graph2(read_group_graph, old_read_group_graph) == false) {
		cout << "graph_hash_of_mixed_weighted_graph1_is_graph2(read_group_graph, old_read_group_graph) == false!" << endl;
		exit(1);
	}
}
#pragma endregion produce_small_graphs_for_experiments_element

#pragma region
void produce_binary_graph_files_for_experiments() {

	int pool_size = 9;
	ThreadPool pool(pool_size); // use pool_size threads
	std::vector< std::future<int> > results;

	/* Jacard distance */
	if (0) {
		bool one_edge_weight = false;

		/*amazon*/
		if (1) {
			string data_name = "amazon";
			int V = 188552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 368552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 548552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
		}

		/*dblp 1248k*/
		if (1) {
			string data_name = "dblp";
			int V = 448891;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 848891;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 1248891;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
		}

		/*movie*/
		if (1) {
			string data_name = "movie";
			int V = 22423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 42423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 62423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_" + to_string(V) + ".bin", data_name + "_read_group_graph_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
		}
	}

	/* one_edge_weight */
	if (1) {
		bool one_edge_weight = true;

		/*amazon*/
		if (1) {
			string data_name = "amazon";
			int V = 188552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 368552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 548552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
		}

		/*dblp 1248k*/
		if (1) {
			string data_name = "dblp";
			int V = 897782;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 1697782;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 2497782;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
		}

		/*movie*/
		if (1) {
			string data_name = "movie";
			int V = 22423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 42423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
			V = 62423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				produce_small_graphs_for_experiments_element(data_name, data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin", data_name + "_read_group_graph_one_edge_weight_" + to_string(V) + ".bin", V, one_edge_weight);
				return 1; }));
		}
	}

}
#pragma endregion produce_binary_graph_files_for_experiments



/*global PLL data; 120 GB*/
int global_dblp_1248891_PLL_indexes_loaded = 0, global_dblp_848891_PLL_indexes_loaded = 0, global_dblp_448891_PLL_indexes_loaded = 0, 
global_movie_PLL_indexes_loaded = 0, global_amazon_PLL_indexes_loaded = 0,
global_dblp_one_edge_weight_2497782_PLL_indexes_loaded = 0, global_dblp_one_edge_weight_1697782_PLL_indexes_loaded = 0, global_dblp_one_edge_weight_897782_PLL_indexes_loaded = 0,
global_movie_one_edge_weight_PLL_indexes_loaded = 0, global_amazon_one_edge_weight_PLL_indexes_loaded = 0; // 0 means is not loading, 1 means is loading, 2 means loaded


vector<vector<PLL_sorted_label>> global_dblp_1248891_PLL_indexes, global_dblp_848891_PLL_indexes, global_dblp_448891_PLL_indexes,
global_movie_62423_PLL_indexes, global_movie_42423_PLL_indexes, global_movie_22423_PLL_indexes,
global_amazon_548552_PLL_indexes, global_amazon_368552_PLL_indexes, global_amazon_188552_PLL_indexes,
global_dblp_one_edge_weight_2497782_PLL_indexes, global_dblp_one_edge_weight_1697782_PLL_indexes, global_dblp_one_edge_weight_897782_PLL_indexes,
global_movie_one_edge_weight_62423_PLL_indexes, global_movie_one_edge_weight_42423_PLL_indexes, global_movie_one_edge_weight_22423_PLL_indexes,
global_amazon_one_edge_weight_548552_PLL_indexes, global_amazon_one_edge_weight_368552_PLL_indexes, global_amazon_one_edge_weight_188552_PLL_indexes;

int max_N_for_exp = 2.5e6;

#ifdef _WIN32
string binary_file_root_path = "F://PLL";
#endif

#ifdef linux
string binary_file_root_path = "PLL";
#endif

#pragma region
void generate_binary_PLL_indexes_element(string data_name, int V, bool one_edge_weight) {

	graph_hash_of_mixed_weighted read_graph;
	string graph_file_name, save_PLL_file_name;
	if (one_edge_weight) {
		graph_file_name = binary_file_root_path + "//" + data_name + "_read_graph_one_edge_weight_" + to_string(V) + ".bin";
		save_PLL_file_name = "PLL_binary_" + data_name + "_one_edge_weight_" + to_string(V) + ".txt";
		read_graph = graph_hash_of_mixed_weighted_binary_read(graph_file_name);
		PLL_generate_and_save_indexes_vectorFORMAT_binary_one_edge_weight(read_graph, save_PLL_file_name, max_N_for_exp);
	}
	else {
		graph_file_name = binary_file_root_path + "//" + data_name + "_read_graph_" + to_string(V) + ".bin";
		save_PLL_file_name = "PLL_binary_" + data_name + "_" + to_string(V) + ".txt";
		read_graph = graph_hash_of_mixed_weighted_binary_read(graph_file_name);
		PLL_generate_and_save_indexes_vectorFORMAT_binary(read_graph, save_PLL_file_name, max_N_for_exp);
	}


	/*test*/
	vector<vector<PLL_sorted_label>> L = PLL_read_indexes_vectorFORMAT_binary(save_PLL_file_name);
	int iteration_source_times = 10, iteration_terminal_times = 100;
	boost::random::uniform_int_distribution<> dist{ static_cast<int>(0), static_cast<int>(V) };

	for (int yy = 0; yy < iteration_source_times; yy++) {
		int source = dist(boost_random_time_seed);

		int mm = 0;
		for (auto it = read_graph.hash_of_vectors.begin(); it != read_graph.hash_of_vectors.end(); it++) {
			if (mm == source) {
				source = it->first;
				break;
			}
			mm++;
		}

		std::unordered_map<int, double> distances;
		std::unordered_map<int, int> predecessors;
		graph_hash_of_mixed_weighted_shortest_paths_source_to_all(read_graph, source, distances, predecessors);
		for (int xx = 0; xx < iteration_terminal_times; xx++) {
			int terminal = dist(boost_random_time_seed);

			int mm = 0;
			for (auto it = read_graph.hash_of_vectors.begin(); it != read_graph.hash_of_vectors.end(); it++) {
				if (mm == terminal) {
					terminal = it->first;
					break;
				}
				mm++;
			}

			double dis = PLL_extract_distance_vectorFORMAT(L, source, terminal);
			if (abs(dis - distances[terminal]) > 1e-5) {
				cout << "source = " << source << endl;
				cout << "terminal = " << terminal << endl;

				cout << "source vector:" << endl;
				for (auto it = L[source].begin(); it != L[source].end(); it++) {
					cout << "<" << it->vertex << "," << it->distance << "," << it->parent_vertex << ">";
				}
				cout << endl;
				cout << "terminal vector:" << endl;
				for (auto it = L[terminal].begin(); it != L[terminal].end(); it++) {
					cout << "<" << it->vertex << "," << it->distance << "," << it->parent_vertex << ">";
				}
				cout << endl;

				cout << "dis = " << dis << endl;
				cout << "distances[terminal] = " << distances[terminal] << endl;
				cout << "abs(dis - distances[terminal]) > 1e-5!" << endl;
				getchar();
			}
			vector<pair<int, int>> path = PLL_extract_shortest_path_vectorFORMAT(L, source, terminal);
			double path_dis = 0;
			if (path.size() == 0) {
				if (source != terminal) { // disconnected
					path_dis = std::numeric_limits<double>::max();
				}
			}
			else {
				for (auto it = path.begin(); it != path.end(); it++) {
					path_dis = path_dis + graph_hash_of_mixed_weighted_edge_weight(read_graph, it->first, it->second);
					if (path_dis > std::numeric_limits<double>::max()) {
						path_dis = std::numeric_limits<double>::max();
					}
				}
			}
			if (abs(dis - path_dis) > 1e-5) {
				cout << "source = " << source << endl;
				cout << "terminal = " << terminal << endl;

				cout << "source vector:" << endl;
				for (auto it = L[source].begin(); it != L[source].end(); it++) {
					cout << "<" << it->vertex << "," << it->distance << "," << it->parent_vertex << ">";
				}
				cout << endl;
				cout << "terminal vector:" << endl;
				for (auto it = L[terminal].begin(); it != L[terminal].end(); it++) {
					cout << "<" << it->vertex << "," << it->distance << "," << it->parent_vertex << ">";
				}
				cout << endl;

				print_vector_pair_int(path);
				cout << "dis = " << dis << endl;
				cout << "path_dis = " << path_dis << endl;
				cout << "abs(dis - path_dis) > 1e-5!" << endl;
				getchar();
			}

		}

	}


}
#pragma endregion generate_binary_PLL_indexes_element

#pragma region
void generate_binary_PLL_indexes() {

	int pool_size = 6;
	ThreadPool pool(pool_size); // use pool_size threads
	std::vector< std::future<int> > results;


	

	/*Jacard dis*/
	if (0) {
		bool one_edge_weight = false;

		/*amazon*/
		if (1) {
			string data_name = "amazon";
			int V = 188552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 368552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 548552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
		}

		/*movie*/
		if (1) {
			string data_name = "movie";
			int V = 22423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 42423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 62423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
		}

		/*dblp*/
		if (1) {
			string data_name = "dblp";
			int V = 448891;
			generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
			V = 848891;
			generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
			V = 1248891;
			generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
		}
	}


	/*one_edge_weight*/
	if (1) {
		bool one_edge_weight = true;

		/*amazon*/
		if (1) {
			string data_name = "amazon";
			int V = 188552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 368552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 548552;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
		}

		/*movie*/
		if (1) {
			string data_name = "movie";
			int V = 22423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 42423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
			V = 62423;
			results.emplace_back(pool.enqueue([data_name, V, one_edge_weight] {
				generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
				return 1; }));
		}

		/*dblp*/
		if (1) {
			string data_name = "dblp";
			int V = 897782;
			generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
			V = 1697782;
			generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
			V = 2497782;
			generate_binary_PLL_indexes_element(data_name, V, one_edge_weight);
		}
	}

}
#pragma endregion generate_binary_PLL_indexes

#pragma region
void load_global_PLL_indexes(string load_name, bool one_edge_weight) {

	if (one_edge_weight) {
		if (load_name == "amazon") {
			if (global_amazon_one_edge_weight_PLL_indexes_loaded == 0) {
				global_amazon_one_edge_weight_PLL_indexes_loaded = 1;
				global_amazon_one_edge_weight_188552_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_amazon_one_edge_weight_188552.txt");
				global_amazon_one_edge_weight_368552_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_amazon_one_edge_weight_368552.txt");
				global_amazon_one_edge_weight_548552_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_amazon_one_edge_weight_548552.txt");
				global_amazon_one_edge_weight_PLL_indexes_loaded = 2;
			}
			else {
				while (global_amazon_one_edge_weight_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "dblp_897782") {
			if (global_dblp_one_edge_weight_897782_PLL_indexes_loaded == 0) {
				global_dblp_one_edge_weight_897782_PLL_indexes_loaded = 1;
				global_dblp_one_edge_weight_897782_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_dblp_one_edge_weight_897782.txt");
				global_dblp_one_edge_weight_897782_PLL_indexes_loaded = 2;
			}
			else {
				while (global_dblp_one_edge_weight_897782_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "dblp_1697782") {
			if (global_dblp_one_edge_weight_1697782_PLL_indexes_loaded == 0) {
				global_dblp_one_edge_weight_1697782_PLL_indexes_loaded = 1;
				global_dblp_one_edge_weight_1697782_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_dblp_one_edge_weight_1697782.txt");
				global_dblp_one_edge_weight_1697782_PLL_indexes_loaded = 2;
			}
			else {
				while (global_dblp_one_edge_weight_1697782_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "dblp_2497782") {
			if (global_dblp_one_edge_weight_2497782_PLL_indexes_loaded == 0) {
				global_dblp_one_edge_weight_2497782_PLL_indexes_loaded = 1;
				global_dblp_one_edge_weight_2497782_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_dblp_one_edge_weight_2497782.txt");
				global_dblp_one_edge_weight_2497782_PLL_indexes_loaded = 2;
			}
			else {
				while (global_dblp_one_edge_weight_2497782_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "movie") {
			if (global_movie_one_edge_weight_PLL_indexes_loaded == 0) {
				global_movie_one_edge_weight_PLL_indexes_loaded = 1;
				global_movie_one_edge_weight_22423_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_movie_one_edge_weight_22423.txt");
				global_movie_one_edge_weight_42423_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_movie_one_edge_weight_42423.txt");
				global_movie_one_edge_weight_62423_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_movie_one_edge_weight_62423.txt");
				global_movie_one_edge_weight_PLL_indexes_loaded = 2;
			}
			else {
				while (global_movie_one_edge_weight_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
	}
	else {
		if (load_name == "amazon") {
			if (global_amazon_PLL_indexes_loaded == 0) {
				global_amazon_PLL_indexes_loaded = 1;
				global_amazon_188552_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_amazon_188552.txt");
				global_amazon_368552_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_amazon_368552.txt");
				global_amazon_548552_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_amazon_548552.txt");
				global_amazon_PLL_indexes_loaded = 2;
			}
			else {
				while (global_amazon_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "dblp_448891") {
			if (global_dblp_448891_PLL_indexes_loaded == 0) {
				global_dblp_448891_PLL_indexes_loaded = 1;
				global_dblp_448891_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_dblp_448891.txt");
				global_dblp_448891_PLL_indexes_loaded = 2;
			}
			else {
				while (global_dblp_448891_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "dblp_848891") {
			if (global_dblp_848891_PLL_indexes_loaded == 0) {
				global_dblp_848891_PLL_indexes_loaded = 1;
				global_dblp_848891_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_dblp_848891.txt");
				global_dblp_848891_PLL_indexes_loaded = 2;
			}
			else {
				while (global_dblp_848891_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "dblp_1248891") {
			if (global_dblp_1248891_PLL_indexes_loaded == 0) {
				global_dblp_1248891_PLL_indexes_loaded = 1;
				global_dblp_1248891_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_dblp_1248891.txt");
				global_dblp_1248891_PLL_indexes_loaded = 2;
			}
			else {
				while (global_dblp_1248891_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
		else if (load_name == "movie") {
			if (global_movie_PLL_indexes_loaded == 0) {
				global_movie_PLL_indexes_loaded = 1;
				global_movie_22423_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_movie_22423.txt");
				global_movie_42423_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_movie_42423.txt");
				global_movie_62423_PLL_indexes = PLL_read_indexes_vectorFORMAT_binary(binary_file_root_path + "//PLL_binary_movie_62423.txt");
				global_movie_PLL_indexes_loaded = 2;
			}
			else {
				while (global_movie_PLL_indexes_loaded != 2) { // is not loaded yet
					; // wait until loaded
				}
			}
		}
	}

}
#pragma endregion load_global_PLL_indexes

#pragma region
void clear_global_PLL_indexes(string load_name, bool one_edge_weight) {

	if (one_edge_weight) {
		if (load_name == "amazon") {
			global_amazon_one_edge_weight_PLL_indexes_loaded = 0;
			global_amazon_one_edge_weight_188552_PLL_indexes.clear();
			global_amazon_one_edge_weight_368552_PLL_indexes.clear();
			global_amazon_one_edge_weight_548552_PLL_indexes.clear();
		}
		else if (load_name == "dblp_897782") {
			global_dblp_one_edge_weight_897782_PLL_indexes_loaded = 0;
			global_dblp_one_edge_weight_897782_PLL_indexes.clear();
		}
		else if (load_name == "dblp_1697782") {
			global_dblp_one_edge_weight_1697782_PLL_indexes_loaded = 0;
			global_dblp_one_edge_weight_1697782_PLL_indexes.clear();
		}
		else if (load_name == "dblp_2497782") {
			global_dblp_one_edge_weight_2497782_PLL_indexes_loaded = 0;
			global_dblp_one_edge_weight_2497782_PLL_indexes.clear();
		}
		else if (load_name == "movie") {
			global_movie_one_edge_weight_PLL_indexes_loaded = 0;
			global_movie_one_edge_weight_22423_PLL_indexes.clear();
			global_movie_one_edge_weight_42423_PLL_indexes.clear();
			global_movie_one_edge_weight_62423_PLL_indexes.clear();
		}
	}
	else {
		if (load_name == "amazon") {
			global_amazon_PLL_indexes_loaded = 0;
			global_amazon_188552_PLL_indexes.clear();
			global_amazon_368552_PLL_indexes.clear();
			global_amazon_548552_PLL_indexes.clear();
		}
		else if (load_name == "dblp_448891") {
			global_dblp_448891_PLL_indexes_loaded = 0;
			global_dblp_448891_PLL_indexes.clear();
		}
		else if (load_name == "dblp_848891") {
			global_dblp_848891_PLL_indexes_loaded = 0;
			global_dblp_848891_PLL_indexes.clear();
		}
		else if (load_name == "dblp_1248891") {
			global_dblp_1248891_PLL_indexes_loaded = 0;
			global_dblp_1248891_PLL_indexes.clear();
		}
		else if (load_name == "movie") {
			global_movie_PLL_indexes_loaded = 0;
			global_movie_22423_PLL_indexes.clear();
			global_movie_42423_PLL_indexes.clear();
			global_movie_62423_PLL_indexes.clear();
		}
	}
}
#pragma endregion clear_global_PLL_indexes

/*experiments code*/

#pragma region
std::unordered_set<int> randomly_sample_feasible_group_vertices(string save_name,
	vector<vector<int>>& cpn, graph_hash_of_mixed_weighted& group_graph, std::unordered_set<int>& all_group_vertices, int T, double b) {

	/* all sampled_group_vertices should be satisfically coverred by max_cpn */

	int max_con_size = 0;
	int max_cpn_id = 0;
	for (int id = cpn.size() - 1; id >= 0; id--) {
		if (max_con_size < (int)cpn[id].size()) { // (int) is required here, why??
			max_con_size = (int)cpn[id].size();
			max_cpn_id = id;
		}
	}
	auto pointer_max_cpn_begin = cpn[max_cpn_id].begin(), pointer_max_cpn_end = cpn[max_cpn_id].end();

	/*find feasible_group_vertices_in_max_cpn*/
	std::unordered_map<int, double> all_group_vertices_not_coverred_probabilities;
	for (auto it = all_group_vertices.begin(); it != all_group_vertices.end(); it++) {
		all_group_vertices_not_coverred_probabilities[*it] = 1;
	}
	for (auto it = pointer_max_cpn_begin; it != pointer_max_cpn_end; it++) {
		int v = *it;
		auto search = group_graph.hash_of_hashs.find(v);
		if (search != group_graph.hash_of_hashs.end()) {
			for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
				int g = it2->first;
				double p_g_v = it2->second;
				double old_p_g_not_coverred = all_group_vertices_not_coverred_probabilities[g];
				all_group_vertices_not_coverred_probabilities[g] = old_p_g_not_coverred * (1 - p_g_v);
			}
		}
		else {
			auto search2 = group_graph.hash_of_vectors.find(v); // if v is not in g, error is here
			for (auto it2 = search2->second.adj_vertices.begin(); it2 != search2->second.adj_vertices.end(); it2++) {
				int g = it2->first;
				double p_g_v = it2->second;
				double old_p_g_not_coverred = all_group_vertices_not_coverred_probabilities[g];
				all_group_vertices_not_coverred_probabilities[g] = old_p_g_not_coverred * (1 - p_g_v);
			}
		}
	}
	vector<int> feasible_group_vertices_in_max_cpn;
	for (auto it = all_group_vertices.begin(); it != all_group_vertices.end(); it++) {
		if (1 - all_group_vertices_not_coverred_probabilities[*it] >= b) {
			feasible_group_vertices_in_max_cpn.push_back(*it);
		}
	}

	/*randomly sample*/
	std::unordered_set<int> sampled_group_vertices;
	if (T > feasible_group_vertices_in_max_cpn.size()) {
		cout << save_name + " Warning: T > feasible_group_vertices_in_max_cpn.size()" << endl;
	}
	else {
		while (sampled_group_vertices.size() < T) {
			boost::random::uniform_int_distribution<> dist{ 0, int(feasible_group_vertices_in_max_cpn.size() - 1) };
			int ID = dist(boost_random_time_seed);
			sampled_group_vertices.insert(feasible_group_vertices_in_max_cpn[ID]);
			feasible_group_vertices_in_max_cpn.erase(feasible_group_vertices_in_max_cpn.begin() + ID);
		}
	}
	return sampled_group_vertices;

}
#pragma endregion randomly_sample_feasible_group_vertices

#pragma region
graph_hash_of_mixed_weighted produce_small_group_graph(std::unordered_set<int>& queried_group_vertices, graph_hash_of_mixed_weighted& subgraph_g, graph_hash_of_mixed_weighted& group_graph) {

	/*group_graph contains and only contains all vertices in queried_group_vertices and subgraph_g*/

	graph_hash_of_mixed_weighted subgraph_group_graph;

	std::unordered_set<int> covered_groups;


	for (auto it = queried_group_vertices.begin(); it != queried_group_vertices.end(); it++) {
		int g = *it;
		graph_hash_of_mixed_weighted_add_vertex(subgraph_group_graph, g, 0);
	}
	for (auto it = subgraph_g.hash_of_vectors.begin(); it != subgraph_g.hash_of_vectors.end(); it++) {
		int v = it->first;
		graph_hash_of_mixed_weighted_add_vertex(subgraph_group_graph, v, 0);
		for (auto it1 = queried_group_vertices.begin(); it1 != queried_group_vertices.end(); it1++) {
			int g = *it1;
			if (graph_hash_of_mixed_weighted_contain_edge(group_graph, v, g)) {
				graph_hash_of_mixed_weighted_add_edge(subgraph_group_graph, v, g, graph_hash_of_mixed_weighted_edge_weight(group_graph, v, g));
				covered_groups.insert(g);
			}
		}
	}

	return subgraph_group_graph;
}
#pragma endregion produce_small_group_graph

#pragma region
void load_graphs(graph_hash_of_mixed_weighted& old_read_graph, graph_hash_of_mixed_weighted& old_read_group_graph, 
	string data_name, int V, bool& generate_new_small_graphs_and_PLL, bool one_edge_weight) {

	if (one_edge_weight) {
		if (data_name == "dblp") {
			if (V == 2497782) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_one_edge_weight_2497782.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_one_edge_weight_2497782.bin");
			}
			else if (V == 1697782) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_one_edge_weight_1697782.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_one_edge_weight_1697782.bin");
			}
			else if (V == 897782) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_one_edge_weight_897782.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_one_edge_weight_897782.bin");
			}
			else {
				generate_new_small_graphs_and_PLL = true;
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_one_edge_weight_2497782.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_one_edge_weight_2497782.bin");
			}
		}
		else if (data_name == "movie") {
			if (V == 62423) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_one_edge_weight_62423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_one_edge_weight_62423.bin");
			}
			else if (V == 42423) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_one_edge_weight_42423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_one_edge_weight_42423.bin");
			}
			else if (V == 22423) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_one_edge_weight_22423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_one_edge_weight_22423.bin");
			}
			else {
				generate_new_small_graphs_and_PLL = true;
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_one_edge_weight_62423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_one_edge_weight_62423.bin");
			}
		}
		else if (data_name == "amazon") {
			if (V == 548552) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_one_edge_weight_548552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read("PLL//amazon_read_group_graph_one_edge_weight_548552.bin");
			}
			else if (V == 368552) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_one_edge_weight_368552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read("PLL//amazon_read_group_graph_one_edge_weight_368552.bin");
			}
			else if (V == 188552) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_one_edge_weight_188552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_group_graph_one_edge_weight_188552.bin");
			}
			else {
				generate_new_small_graphs_and_PLL = true;
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_one_edge_weight_548552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_group_graph_one_edge_weight_548552.bin");
			}
		}
	}
	else {
		if (data_name == "dblp") {
			if (V == 1248891) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_1248891.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_1248891.bin");
			}
			else if (V == 848891) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_848891.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_848891.bin");
			}
			else if (V == 448891) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_448891.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_448891.bin");
			}
			else {
				generate_new_small_graphs_and_PLL = true;
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_graph_1248891.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//dblp_read_group_graph_1248891.bin");
			}
		}
		else if (data_name == "movie") {
			if (V == 62423) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_62423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_62423.bin");
			}
			else if (V == 42423) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_42423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_42423.bin");
			}
			else if (V == 22423) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_22423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_22423.bin");
			}
			else {
				generate_new_small_graphs_and_PLL = true;
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_graph_62423.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//movie_read_group_graph_62423.bin");
			}
		}
		else if (data_name == "amazon") {
			if (V == 548552) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_548552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read("PLL//amazon_read_group_graph_548552.bin");
			}
			else if (V == 368552) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_368552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read("PLL//amazon_read_group_graph_368552.bin");
			}
			else if (V == 188552) {
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_188552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_group_graph_188552.bin");
			}
			else {
				generate_new_small_graphs_and_PLL = true;
				old_read_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_graph_548552.bin");
				old_read_group_graph = graph_hash_of_mixed_weighted_binary_read(binary_file_root_path + "//amazon_read_group_graph_548552.bin");
			}
		}
	}

}
#pragma endregion load_graphs

#pragma region
void call_algorithms(graph_v_of_v_idealID& input_graph, graph_v_of_v_idealID& input_group_graph, std::unordered_set<int>& compulsory_group_vertices,
	vector<int>& graph_id_2_PLL_id, vector<int>& PLL_id_2_graph_id,
	vector<vector<PLL_sorted_label>>& PLL_indexes, double b, double tau,
	bool use_ENSteiner, bool use_PrunedDPPP, bool use_ImprovAPP, bool use_DUAL, bool use_GRETREE, bool use_GREPATH, bool use_DPBF,
	double& time_ENSteiner, double& time_PrunedDPPP, double& time_ImprovAPP, double& time_DUAL, double& time_GRETREE, double& time_GREPATH, double& time_DPBF,
	double& time_ENSteiner_P, double& time_PrunedDPPP_P, double& time_ImprovAPP_P, double& time_DUAL_P, double& time_GRETREE_P, double& time_GREPATH_P, double& time_DPBF_P,
	double& final_cost_ENSteiner, double& final_cost_PrunedDPPP, double& final_cost_ImprovAPP, double& final_cost_DUAL, double& final_cost_GRETREE, double& final_cost_GREPATH, double& final_cost_DPBF,
	double& final_cost_ENSteiner_P, double& final_cost_PrunedDPPP_P, double& final_cost_ImprovAPP_P, double& final_cost_DUAL_P, double& final_cost_GRETREE_P, double& final_cost_GREPATH_P, double& final_cost_DPBF_P) {

	if (use_ENSteiner) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = ENSteiner(input_graph, input_group_graph, compulsory_group_vertices);
		solu = make_solutree_feasible(input_graph, input_group_graph, compulsory_group_vertices, solu, b, PLL_indexes, graph_id_2_PLL_id, PLL_id_2_graph_id);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_ENSteiner = time_ENSteiner + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_ENSteiner > cost) {
			final_cost_ENSteiner = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_ENSteiner_P = time_ENSteiner_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_ENSteiner_P > cost) {
			final_cost_ENSteiner_P = cost;
		}
	}

	if (use_DPBF) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = graph_v_of_v_idealID_DPBF_only_ec(input_graph, input_group_graph, compulsory_group_vertices);
		solu = make_solutree_feasible(input_graph, input_group_graph, compulsory_group_vertices, solu, b, PLL_indexes, graph_id_2_PLL_id, PLL_id_2_graph_id);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_DPBF = time_DPBF + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_DPBF > cost) {
			final_cost_DPBF = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_DPBF_P = time_DPBF_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_DPBF_P > cost) {
			final_cost_DPBF_P = cost;
		}
	}

	if (use_PrunedDPPP) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = graph_v_of_v_idealID_PrunedDPPlusPlus(input_graph, input_group_graph, compulsory_group_vertices, tau);
		solu = make_solutree_feasible(input_graph, input_group_graph, compulsory_group_vertices, solu, b, PLL_indexes, graph_id_2_PLL_id, PLL_id_2_graph_id);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_PrunedDPPP = time_PrunedDPPP + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_PrunedDPPP > cost) {
			final_cost_PrunedDPPP = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_PrunedDPPP_P = time_PrunedDPPP_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_PrunedDPPP_P > cost) {
			final_cost_PrunedDPPP_P = cost;
		}
	}

	if (use_ImprovAPP) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = ImprovAPP_onlyec(input_graph, input_group_graph, compulsory_group_vertices);
		solu = make_solutree_feasible(input_graph, input_group_graph, compulsory_group_vertices, solu, b, PLL_indexes, graph_id_2_PLL_id, PLL_id_2_graph_id);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_ImprovAPP = time_ImprovAPP + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_ImprovAPP > cost) {
			final_cost_ImprovAPP = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_ImprovAPP_P = time_ImprovAPP_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_ImprovAPP_P > cost) {
			final_cost_ImprovAPP_P = cost;
		}
	}

	if (use_DUAL) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = algo1_DUAL_graph_v_of_v_idealID(input_graph, input_group_graph, compulsory_group_vertices, b, tau);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_DUAL = time_DUAL + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_DUAL > cost) {
			final_cost_DUAL = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_DUAL_P = time_DUAL_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_DUAL_P > cost) {
			final_cost_DUAL_P = cost;
		}
	}

	if (use_GRETREE) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = algo2_GRETREE_graph_v_of_v_idealID(input_graph, input_group_graph, compulsory_group_vertices, b, tau);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_GRETREE = time_GRETREE + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_GRETREE > cost) {
			final_cost_GRETREE = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_GRETREE_P = time_GRETREE_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_GRETREE_P > cost) {
			final_cost_GRETREE_P = cost;
		}
	}

	if (use_GREPATH) {
		auto begin = std::chrono::high_resolution_clock::now();
		graph_hash_of_mixed_weighted solu = algo3_GREPATH_graph_v_of_v_idealID(input_graph, input_group_graph, compulsory_group_vertices, b, tau, PLL_indexes, graph_id_2_PLL_id, PLL_id_2_graph_id);
		auto end = std::chrono::high_resolution_clock::now();
		double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
		time_GREPATH = time_GREPATH + (double)runningtime;
		double cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_GREPATH > cost) {
			final_cost_GREPATH = cost;
		}
		auto begin2 = std::chrono::high_resolution_clock::now();
		remove_redundent_leaves_graph_v_of_v_idealID(solu, input_group_graph, compulsory_group_vertices, b);
		auto end2 = std::chrono::high_resolution_clock::now();
		double runningtime2 = std::chrono::duration_cast<std::chrono::nanoseconds>(end2 - begin2).count() / 1e9; // s
		time_GREPATH_P = time_GREPATH_P + (double)runningtime2;
		cost = graph_hash_of_mixed_weighted_sum_of_ec(solu);
		if (final_cost_GREPATH_P > cost) {
			final_cost_GREPATH_P = cost;
		}
	}
}
#pragma endregion call_algorithms

#pragma region
int experiment_element(string data_name, string save_name, int V, int T, double b, double tau, double P_min, double P_max, int iteration_times,
	bool use_ENSteiner, bool use_PrunedDPPP, bool use_ImprovAPP, bool use_DUAL, bool use_GRETREE, bool use_GREPATH, bool use_DPBF, bool one_edge_weight) {

	/*output*/
	ofstream outputFile;
	outputFile.precision(6);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "V,T,b,tau,P_min,P_max," <<
		"cost_ENSteiner,time_ENSteiner,cost_PrunedDPPP,time_PrunedDPPP,cost_ImprovAPP,time_ImprovAPP," <<
		"cost_DUAL,time_DUAL,cost_GRETREE,time_GRETREE,cost_GREPATH,time_GREPATH,cost_DPBF,time_DPBF," <<
	"cost_ENSteiner_P,time_ENSteiner_P,cost_PrunedDPPP_P,time_PrunedDPPP_P,cost_ImprovAPP_P,time_ImprovAPP_P," <<
		"cost_DUAL_P,time_DUAL_P,cost_GRETREE_P,time_GRETREE_P,cost_GREPATH_P,time_GREPATH_P,cost_DPBF_P,time_DPBF_P" << endl;

	/*read data*/
	graph_hash_of_mixed_weighted old_read_graph, old_read_group_graph;
	bool generate_new_small_graphs_and_PLL = false;
	load_graphs(old_read_graph, old_read_group_graph, data_name, V, generate_new_small_graphs_and_PLL, one_edge_weight);
	graph_hash_of_mixed_weighted_ec_normalization_with_range(old_read_group_graph, P_min, P_max); // probability of v-g is weight of edge (v,g) in old_read_group_graph

	/*find cpn*/
	vector<vector<int>> cpn;

	/*iterations*/
	for (int times = 1; times <= iteration_times; times++) {

		cout << save_name << " iteration_times: " << times << " out of " << iteration_times << endl;

		/*randomly sample small graphs*/
		std::unordered_set<int> sampled_group_vertices;
		bool sampled_group_vertices_is_feasible = false;

		vector<vector<PLL_sorted_label>> newly_generated_PLL_indexes; // newly_generated_PLL_indexes is used when need_to_generate_PLL_indexes=true, otherwise global indexes are used
		if (generate_new_small_graphs_and_PLL) {

			unordered_set<int> selected_vertices = graph_hash_of_mixed_weighted_breadth_first_search_a_fixed_number_of_vertices_in_unconnected_graphs_start_from_maxcpn(old_read_graph, V);
			graph_hash_of_mixed_weighted small_read_graph = graph_hash_of_mixed_weighted_extract_subgraph_for_a_hash_of_vertices(old_read_graph, selected_vertices);

			/*compute small_read_graph_group_vertices and sampled_group_vertices*/
			std::unordered_set<int> small_read_graph_group_vertices;
			for (auto it = small_read_graph.hash_of_vectors.begin(); it != small_read_graph.hash_of_vectors.end(); it++) {
				int v = it->first;
				auto search = old_read_group_graph.hash_of_hashs.find(v);
				if (search != old_read_group_graph.hash_of_hashs.end()) {
					for (auto it2 = search->second.begin(); it2 != search->second.end(); it2++) {
						small_read_graph_group_vertices.insert(it2->first);
					}
				}
				else {
					auto search3 = old_read_group_graph.hash_of_vectors.find(v);
					for (auto it2 = search3->second.adj_vertices.begin(); it2 != search3->second.adj_vertices.end(); it2++) {
						small_read_graph_group_vertices.insert(it2->first);
					}
				}
			}

			if (T > small_read_graph_group_vertices.size()) {
				cout << save_name + " Warning: T > small_read_graph_group_vertices.size()" << endl;
				times--;
				continue;
			}
			cpn = graph_hash_of_mixed_weighted_connected_components_vector_format(small_read_graph, old_read_graph.hash_of_vectors.size()); // small_read_graph is needed here

			sampled_group_vertices = randomly_sample_feasible_group_vertices(save_name, cpn, old_read_group_graph, small_read_graph_group_vertices, T, b);
			if (T > sampled_group_vertices.size()) {
				times--;
				continue;
			}

			newly_generated_PLL_indexes = PLL_generate_indexes_vectorFORMAT(small_read_graph, old_read_graph.hash_of_vectors.size() + 1);
		}
		else {
			cpn = graph_hash_of_mixed_weighted_connected_components_vector_format(old_read_graph, max_N_for_exp);

			std::unordered_set<int> old_group_vertices;
			for (auto it = old_read_group_graph.hash_of_vectors.begin(); it != old_read_group_graph.hash_of_vectors.end(); it++) {
				if (old_read_graph.hash_of_vectors.count(it->first) == 0) {
					old_group_vertices.insert(it->first);
				}
			}

			sampled_group_vertices = randomly_sample_feasible_group_vertices(save_name, cpn, old_read_group_graph, old_group_vertices, T, b);
			if (T > sampled_group_vertices.size()) {
				times--;
				continue;
			}
		}

		/*solve instance in each maximal component*/
		double time_ENSteiner = 0, time_PrunedDPPP = 0, time_ImprovAPP = 0, time_DUAL = 0, time_GREPATH = 0, time_GRETREE = 0, time_DPBF = 0,
			time_ENSteiner_P = 0, time_PrunedDPPP_P = 0, time_ImprovAPP_P = 0, time_DUAL_P = 0, time_GREPATH_P = 0, time_GRETREE_P = 0, time_DPBF_P = 0;

		double final_cost_ENSteiner = INT_MAX, final_cost_PrunedDPPP = INT_MAX, final_cost_ImprovAPP = INT_MAX,
			final_cost_DUAL = INT_MAX, final_cost_GREPATH = INT_MAX, final_cost_GRETREE = INT_MAX, final_cost_DPBF = INT_MAX,
			final_cost_ENSteiner_P = INT_MAX, final_cost_PrunedDPPP_P = INT_MAX, final_cost_ImprovAPP_P = INT_MAX,
			final_cost_DUAL_P = INT_MAX, final_cost_GREPATH_P = INT_MAX, final_cost_GRETREE_P = INT_MAX, final_cost_DPBF_P = INT_MAX;

		int g_min_size = 0; // this g_min is the sum of all g_mins in all components

		vector<int> graph_id_2_PLL_id(max_N_for_exp), PLL_id_2_graph_id(max_N_for_exp);

		for (auto i = cpn.begin(); i != cpn.end(); i++) {

			graph_hash_of_mixed_weighted subgraph_g = graph_hash_of_mixed_weighted_extract_subgraph(old_read_graph, *i);

			graph_hash_of_mixed_weighted subgraph_g_group_graph = produce_small_group_graph(sampled_group_vertices, subgraph_g, old_read_group_graph);

			int g_min = find_g_min(subgraph_g_group_graph, sampled_group_vertices); // find g_min
			g_min_size = g_min_size + subgraph_g_group_graph.degree(g_min);
			//cout << "subgraph_g_group_graph.degree(g_min): " << subgraph_g_group_graph.degree(g_min) << endl;

			if (there_is_a_feasible_PGST_in_this_cpn(subgraph_g, subgraph_g_group_graph, sampled_group_vertices, b)) {

				sampled_group_vertices_is_feasible = true;

				/*idealize vertexIDs*/
				unordered_map<int, int> vertexID_old_to_new;
				int id = 0;
				for (auto it = subgraph_g.hash_of_vectors.begin(); it != subgraph_g.hash_of_vectors.end(); it++) {
					vertexID_old_to_new[it->first] = id;
					graph_id_2_PLL_id[id] = it->first;
					PLL_id_2_graph_id[it->first] = id;
					id++;
				}
				std::unordered_set<int> sampled_group_vertices_idealID;
				for (auto it = sampled_group_vertices.begin(); it != sampled_group_vertices.end(); it++) {
					vertexID_old_to_new[*it] = id;
					sampled_group_vertices_idealID.insert(id);
					id++;
				}
				graph_v_of_v_idealID subgraph_g_idealID = graph_hash_of_mixed_weighted_to_graph_v_of_v_idealID(subgraph_g, vertexID_old_to_new);
				graph_v_of_v_idealID subgraph_g_group_graph_idealID = graph_hash_of_mixed_weighted_to_graph_v_of_v_idealID(subgraph_g_group_graph, vertexID_old_to_new);
				subgraph_g.clear();
				subgraph_g_group_graph.clear();
				vertexID_old_to_new.clear();


				auto PLL_indexes_pointer = &newly_generated_PLL_indexes;
				if (one_edge_weight) {
					if (data_name == "dblp") {
						if (V == 2497782) {
							PLL_indexes_pointer = &global_dblp_one_edge_weight_2497782_PLL_indexes;
						}
						else if (V == 1697782) {
							PLL_indexes_pointer = &global_dblp_one_edge_weight_1697782_PLL_indexes;
						}
						else if (V == 897782) {
							PLL_indexes_pointer = &global_dblp_one_edge_weight_897782_PLL_indexes;
						}
					}
					else if (data_name == "movie") {
						if (V == 62423) {
							PLL_indexes_pointer = &global_movie_one_edge_weight_62423_PLL_indexes;
						}
						else if (V == 42423) {
							PLL_indexes_pointer = &global_movie_one_edge_weight_42423_PLL_indexes;
						}
						else if (V == 22423) {
							PLL_indexes_pointer = &global_movie_one_edge_weight_22423_PLL_indexes;
						}
					}
					else if (data_name == "amazon") {
						if (V == 548552) {
							PLL_indexes_pointer = &global_amazon_one_edge_weight_548552_PLL_indexes;
						}
						else if (V == 368552) {
							PLL_indexes_pointer = &global_amazon_one_edge_weight_368552_PLL_indexes;
						}
						else if (V == 188552) {
							PLL_indexes_pointer = &global_amazon_one_edge_weight_188552_PLL_indexes;
						}
					}
				}
				else {
					if (data_name == "dblp") {
						if (V == 1248891) {
							PLL_indexes_pointer = &global_dblp_1248891_PLL_indexes;
						}
						else if (V == 848891) {
							PLL_indexes_pointer = &global_dblp_848891_PLL_indexes;
						}
						else if (V == 448891) {
							PLL_indexes_pointer = &global_dblp_448891_PLL_indexes;
						}
					}
					else if (data_name == "movie") {
						if (V == 62423) {
							PLL_indexes_pointer = &global_movie_62423_PLL_indexes;
						}
						else if (V == 42423) {
							PLL_indexes_pointer = &global_movie_42423_PLL_indexes;
						}
						else if (V == 22423) {
							PLL_indexes_pointer = &global_movie_22423_PLL_indexes;
						}
					}
					else if (data_name == "amazon") {
						if (V == 548552) {
							PLL_indexes_pointer = &global_amazon_548552_PLL_indexes;
						}
						else if (V == 368552) {
							PLL_indexes_pointer = &global_amazon_368552_PLL_indexes;
						}
						else if (V == 188552) {
							PLL_indexes_pointer = &global_amazon_188552_PLL_indexes;
						}
					}
				}

				call_algorithms(subgraph_g_idealID, subgraph_g_group_graph_idealID, sampled_group_vertices_idealID, graph_id_2_PLL_id, PLL_id_2_graph_id,
					*PLL_indexes_pointer, b, tau, use_ENSteiner, use_PrunedDPPP, use_ImprovAPP, use_DUAL, use_GRETREE, use_GREPATH, use_DPBF,
					time_ENSteiner, time_PrunedDPPP, time_ImprovAPP, time_DUAL, time_GRETREE, time_GREPATH, time_DPBF,
					time_ENSteiner_P, time_PrunedDPPP_P, time_ImprovAPP_P, time_DUAL_P, time_GRETREE_P, time_GREPATH_P, time_DPBF_P,
					final_cost_ENSteiner, final_cost_PrunedDPPP, final_cost_ImprovAPP, final_cost_DUAL, final_cost_GRETREE, final_cost_GREPATH, final_cost_DPBF,
					final_cost_ENSteiner_P, final_cost_PrunedDPPP_P, final_cost_ImprovAPP_P, final_cost_DUAL_P, final_cost_GRETREE_P, final_cost_GREPATH_P, final_cost_DPBF_P);

			}
		}

		if (sampled_group_vertices_is_feasible == true) { // there is a feasible solution
			outputFile << V << "," << T << "," << b
				<< "," << tau << "," << P_min << "," << P_max << ","
				<< final_cost_ENSteiner << "," << time_ENSteiner << "," << final_cost_PrunedDPPP << "," << time_PrunedDPPP
				<< "," << final_cost_ImprovAPP << "," << time_ImprovAPP << "," << final_cost_DUAL << "," << time_DUAL
				<< "," << final_cost_GRETREE << "," << time_GRETREE << "," << final_cost_GREPATH << "," << time_GREPATH << "," << final_cost_DPBF << "," << time_DPBF << ","
			<< final_cost_ENSteiner_P << "," << time_ENSteiner_P << "," << final_cost_PrunedDPPP_P << "," << time_PrunedDPPP_P
				<< "," << final_cost_ImprovAPP_P << "," << time_ImprovAPP_P << "," << final_cost_DUAL_P << "," << time_DUAL_P
				<< "," << final_cost_GRETREE_P << "," << time_GRETREE_P << "," << final_cost_GREPATH_P << "," << time_GREPATH_P << "," << final_cost_DPBF_P << "," << time_DPBF_P << endl;
		}
		else {
			times--;
		}


	}

	return 1;

}
#pragma endregion experiment_element

#pragma region
void V1_experiments() {

	/* only DUAL and GRETREE do not need PLL indexes */

	int pool_size = 40; // 20 is too many for full dblp 1ec£¬ while 15 uses 350GB RAM at most
	ThreadPool pool(pool_size); // use pool_size threads
	std::vector< std::future<int> > results;

	/*Jacard*/
	if (0) {
		bool one_edge_weight = false;

		/*amazon*/
		if (0) {

			string data_name = "amazon";
			int iteration_times = 100;
			int V = 548552, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_1_" + to_string(ii) + ".csv", 45, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, true, true, true, true, one_edge_weight);
						return 1; })); // DUAL is sometimes very slow when V=70
				}
			}
		}

		/*movie 22 threads; 150 GB RAM*/
		if (0) {

			string data_name = "movie";
			int iteration_times = 100;
			int V = 62423, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;


			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_1_" + to_string(ii) + ".csv", 70, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, true, true, true, true, one_edge_weight);
						return 1; }));
				}
			}


		}

		/*dblp*/
		if (0) {

			string data_name = "dblp";

			int iteration_times = 100;

			int V = 1248891, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			/*others*/
			if (1) {
				int split_num = 10;
				for (int ii = 1; ii <= split_num; ii++) {

					/*vary V; 200 GB*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_V_1_" + to_string(ii) + ".csv", 90, T, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, true, true, true, true, one_edge_weight);
						}));
					}

				}
			}

		}

	}


	/*one_edge_weight*/
	if (1) {
		bool one_edge_weight = true;

		/*amazon*/
		if (0) {

			string data_name = "amazon";
			int iteration_times = 100;
			int V = 548552, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_1_" + to_string(ii) + ".csv", 45, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, true, true, true, true, one_edge_weight); // 50 is sometimes too slow
						return 1; }));
				}
			}

		}

		/*movie*/
		if (0) {

			string data_name = "movie";
			int iteration_times = 100;
			int V = 62423, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_1_" + to_string(ii) + ".csv", 70, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, true, true, true, true, one_edge_weight);
						return 1; }));
				}

			}

		}

		/*dblp 27 threads*/
		if (1) {

			string data_name = "dblp";
			int iteration_times = 100;
			int V = 2497782, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			/*others*/
			if (1) {
				int split_num = 10;
				for (int ii = 1; ii <= split_num; ii++) {

					/*vary V*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_1_" + to_string(ii) + ".csv", 90, T, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, true, true, true, true, one_edge_weight);
							return 1; }));
					}

				}
			}

		}
	}

}
#pragma endregion V1_experiments

#pragma region
void experiments() {

	/* only DUAL and GRETREE do not need PLL indexes */

	int pool_size = 30; // 20 is too many for full dblp 1ec£¬ while 15 uses 350GB RAM at most
	ThreadPool pool(pool_size); // use pool_size threads
	std::vector< std::future<int> > results;

	/*Jacard*/
	if (1) {
		bool one_edge_weight = false;

		/*amazon*/
		if (0) {

			string data_name = "amazon";
			load_global_PLL_indexes(data_name, one_edge_weight);
			int iteration_times = 100;
			int V = 548552, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					//results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
					//	experiment_element(data_name, "Exp_" + data_name + "_vary_V_1_" + to_string(ii) + ".csv", 45, T, b, tau, P_min, P_max, iteration_times / split_num,
					//		true, true, true, true, true, true, true, one_edge_weight);
					//	return 1; })); // DUAL is often very slow when V=70, sometimes even when V=50
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_2_" + to_string(ii) + ".csv", 188552, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_3_" + to_string(ii) + ".csv", 368552, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary T*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_T_1_" + to_string(ii) + ".csv", V, 3, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_T_2_" + to_string(ii) + ".csv", V, 4, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_T_3_" + to_string(ii) + ".csv", V, 6, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary b*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_b_1_" + to_string(ii) + ".csv", V, T, 0.8, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_b_2_" + to_string(ii) + ".csv", V, T, 0.85, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_b_3_" + to_string(ii) + ".csv", V, T, 0.95, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary tau*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_tau_1_" + to_string(ii) + ".csv", V, T, b, 3, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, true, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_tau_2_" + to_string(ii) + ".csv", V, T, b, 5, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, true, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_tau_3_" + to_string(ii) + ".csv", V, T, b, 7, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, true, 0, 0, one_edge_weight);
						return 1; }));
				}

				/*vary P_min*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_1_" + to_string(ii) + ".csv", V, T, b, tau, 0.4, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_2_" + to_string(ii) + ".csv", V, T, b, tau, 0.6, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_3_" + to_string(ii) + ".csv", V, T, b, tau, 0.7, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary P_max*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_1_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.7, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_2_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.8, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_3_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 1, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}


				
			}

			
		}

		/*movie 22 threads; 150 GB RAM*/
		if (1) {

			string data_name = "movie";
			load_global_PLL_indexes(data_name, one_edge_weight);
			int iteration_times = 100;
			int V = 62423, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;


			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {
				
				/*vary V*/
				if (1) {
					//results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
					//	experiment_element(data_name, "Exp_" + data_name + "_vary_V_1_" + to_string(ii) + ".csv", 70, T, b, tau, P_min, P_max, iteration_times / split_num, 
					//		true, true, true, true, true, true, true, one_edge_weight);
					//	return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_special_" + to_string(ii) + ".csv", 2423, T, b, tau, P_min, P_max, iteration_times / split_num / 2,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_2_" + to_string(ii) + ".csv", 22423, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_V_3_" + to_string(ii) + ".csv", 42423, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary T*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_T_1_" + to_string(ii) + ".csv", V, 3, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_T_2_" + to_string(ii) + ".csv", V, 4, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_T_3_" + to_string(ii) + ".csv", V, 6, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary b*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_b_1_" + to_string(ii) + ".csv", V, T, 0.8, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_b_2_" + to_string(ii) + ".csv", V, T, 0.85, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_b_3_" + to_string(ii) + ".csv", V, T, 0.95, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary tau*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_tau_1_" + to_string(ii) + ".csv", V, T, b, 3, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, 0, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_tau_2_" + to_string(ii) + ".csv", V, T, b, 5, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, 0, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_tau_3_" + to_string(ii) + ".csv", V, T, b, 7, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, 0, 0, 0, one_edge_weight);
						return 1; }));
				}

				/*vary P_min*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_1_" + to_string(ii) + ".csv", V, T, b, tau, 0.4, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_2_" + to_string(ii) + ".csv", V, T, b, tau, 0.6, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_3_" + to_string(ii) + ".csv", V, T, b, tau, 0.7, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary P_max*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_1_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.7, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_2_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.8, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_3_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 1, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}



			}

			
		}

		for (auto&& result : results) {
			result.get(); // wait for the below clear
		}
		results.clear();
		clear_global_PLL_indexes("amazon", one_edge_weight);
		clear_global_PLL_indexes("movie", one_edge_weight);

		/*dblp*/
		if (0) {

			string data_name = "dblp";

			int iteration_times = 100;

			int V = 1248891, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			/*V2; V3*/
			if (1) {

				int split_num = 20;

				load_global_PLL_indexes("dblp_448891", one_edge_weight);
				for (int ii = 1; ii <= split_num; ii++) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						return experiment_element(data_name, "Exp_" + data_name + "_vary_V_2_" + to_string(ii) + ".csv", 448891, T, b, tau, P_min, P_max,
							iteration_times / split_num, true, true, true, 0, true, true, true, one_edge_weight);
					}));
				}
				for (auto&& result : results) {
					result.get(); // to finish the above threads; since the amazon and movie threads return 1, but not return experiment_element value, amazon and movie threads do not need to be finished here
				}
				results.clear(); // future get value can only be called once for each thread result, must clear results here, otherwise you should not call the above future value again!
				clear_global_PLL_indexes("dblp_448891", one_edge_weight); // to save memory


				load_global_PLL_indexes("dblp_848891", one_edge_weight);
				for (int ii = 1; ii <= split_num; ii++) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						return experiment_element(data_name, "Exp_" + data_name + "_vary_V_3_" + to_string(ii) + ".csv", 848891, T, b, tau, P_min, P_max, 
							iteration_times / split_num, true, true, true, 0, 0, true, true, one_edge_weight);
					}));
				}
				for (auto&& result : results) {
					result.get(); // since V2 future values have been cleared above, it's safe to get all futures values in reults here
				}
				results.clear();
				clear_global_PLL_indexes("dblp_848891", one_edge_weight);

			}

			/*others*/
			if (1) {
				load_global_PLL_indexes("dblp_1248891", one_edge_weight);
				int split_num = 10;
				for (int ii = 1; ii <= split_num; ii++) {

					/*vary V; 200 GB*/
					if (1) {
						//results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						//	return experiment_element(data_name, "Exp_" + data_name + "_vary_V_1_" + to_string(ii) + ".csv", 90, T, b, tau, P_min, P_max, iteration_times / split_num,
						//		true, true, true, true, true, true, true, one_edge_weight);
						//}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
					}

					/*vary T*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_T_1_" + to_string(ii) + ".csv", V, 3, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_T_2_" + to_string(ii) + ".csv", V, 4, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_T_3_" + to_string(ii) + ".csv", V, 6, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
					}

					/*vary b*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_b_1_" + to_string(ii) + ".csv", V, T, 0.8, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_b_2_" + to_string(ii) + ".csv", V, T, 0.85, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_b_3_" + to_string(ii) + ".csv", V, T, 0.95, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
					}

					/*vary tau*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_tau_1_" + to_string(ii) + ".csv", V, T, b, 3, P_min, P_max, iteration_times / split_num,
								0, true, 0, 0, 0, 0, 0, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_tau_2_" + to_string(ii) + ".csv", V, T, b, 5, P_min, P_max, iteration_times / split_num,
								0, true, 0, 0, 0, 0, 0, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_tau_3_" + to_string(ii) + ".csv", V, T, b, 7, P_min, P_max, iteration_times / split_num,
								0, true, 0, 0, 0, 0, 0, one_edge_weight);
						}));
					}

					/*vary P_min*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_1_" + to_string(ii) + ".csv", V, T, b, tau, 0.4, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_2_" + to_string(ii) + ".csv", V, T, b, tau, 0.6, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_P_min_3_" + to_string(ii) + ".csv", V, T, b, tau, 0.7, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
					}

					/*vary P_max*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_1_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.7, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_2_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.8, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_vary_P_max_3_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 1, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
						}));
					}

				}
				for (auto&& result : results) {
					result.get(); // wait for the below clear
				}
				results.clear();
				clear_global_PLL_indexes("dblp_1248891", one_edge_weight);
			}
			
		}

	}


	/*one_edge_weight*/
	if (1) {
		bool one_edge_weight = true;

		/*amazon*/
		if (0) {

			string data_name = "amazon";
			load_global_PLL_indexes(data_name, one_edge_weight);
			int iteration_times = 100;
			int V = 548552, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					//results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
					//	experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_1_" + to_string(ii) + ".csv", 45, T, b, tau, P_min, P_max, iteration_times / split_num, 
					//		true, true, true, true, true, true, true, one_edge_weight); // 50 is sometimes too slow
					//	return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_2_" + to_string(ii) + ".csv", 188552, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_3_" + to_string(ii) + ".csv", 368552, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary T*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_1_" + to_string(ii) + ".csv", V, 3, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_2_" + to_string(ii) + ".csv", V, 4, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_3_" + to_string(ii) + ".csv", V, 6, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary b*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_1_" + to_string(ii) + ".csv", V, T, 0.8, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_2_" + to_string(ii) + ".csv", V, T, 0.85, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_3_" + to_string(ii) + ".csv", V, T, 0.95, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary tau*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_1_" + to_string(ii) + ".csv", V, T, b, 3, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, true, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_2_" + to_string(ii) + ".csv", V, T, b, 5, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, true, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_3_" + to_string(ii) + ".csv", V, T, b, 7, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, true, 0, 0, one_edge_weight);
						return 1; }));
				}

				/*vary P_min*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_1_" + to_string(ii) + ".csv", V, T, b, tau, 0.4, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_2_" + to_string(ii) + ".csv", V, T, b, tau, 0.6, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_3_" + to_string(ii) + ".csv", V, T, b, tau, 0.7, P_max, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary P_max*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_1_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.7, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_2_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.8, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_3_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 1, iteration_times / split_num,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
				}


				
			}
		
		}

		/*movie*/
		if (0) {

			string data_name = "movie";
			load_global_PLL_indexes(data_name, one_edge_weight);
			int iteration_times = 100;
			int V = 62423, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {

				/*vary V*/
				if (1) {
					//results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
					//	experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_1_" + to_string(ii) + ".csv", 70, T, b, tau, P_min, P_max, iteration_times / split_num,
					//		true, true, true, true, true, true, true, one_edge_weight);
					//	return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_special_" + to_string(ii) + ".csv", 2423, T, b, tau, P_min, P_max, iteration_times / split_num / 2,
							true, true, true, 0, true, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_2_" + to_string(ii) + ".csv", 22423, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_3_" + to_string(ii) + ".csv", 42423, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary T*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_1_" + to_string(ii) + ".csv", V, 3, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_2_" + to_string(ii) + ".csv", V, 4, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_3_" + to_string(ii) + ".csv", V, 6, b, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary b*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_1_" + to_string(ii) + ".csv", V, T, 0.8, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_2_" + to_string(ii) + ".csv", V, T, 0.85, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_3_" + to_string(ii) + ".csv", V, T, 0.95, tau, P_min, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary tau*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_1_" + to_string(ii) + ".csv", V, T, b, 3, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, 0, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_2_" + to_string(ii) + ".csv", V, T, b, 5, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, 0, 0, 0, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_3_" + to_string(ii) + ".csv", V, T, b, 7, P_min, P_max, iteration_times / split_num,
							0, true, 0, 0, 0, 0, 0, one_edge_weight);
						return 1; }));
				}

				/*vary P_min*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_1_" + to_string(ii) + ".csv", V, T, b, tau, 0.4, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_2_" + to_string(ii) + ".csv", V, T, b, tau, 0.6, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_3_" + to_string(ii) + ".csv", V, T, b, tau, 0.7, P_max, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

				/*vary P_max*/
				if (1) {
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_1_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.7, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_2_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.8, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
					results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_3_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 1, iteration_times / split_num,
							true, true, true, 0, 0, true, true, one_edge_weight);
						return 1; }));
				}

			}

		}

		for (auto&& result : results) {
			result.get(); // wait for the below clear
		}
		results.clear();
		clear_global_PLL_indexes("amazon", one_edge_weight);
		clear_global_PLL_indexes("movie", one_edge_weight);

		/*dblp 27 threads*/
		if (1) {

			int pool_size = 15; // 20 is too many for full dblp 1ec£¬ while 15 uses 350GB RAM at most
			ThreadPool pool(pool_size); // use pool_size threads
			std::vector< std::future<int> > results;

			string data_name = "dblp";
			int iteration_times = 100;
			int V = 2497782, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			/*V2; V3*/
			if (1) {

				int split_num = 20;
				if (1) {
					load_global_PLL_indexes("dblp_897782", one_edge_weight);
					for (int ii = 1; ii <= split_num; ii++) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_2_" + to_string(ii) + ".csv", 897782, T, b, tau, P_min, P_max,
								iteration_times / split_num, true, true, true, 0, true, true, true, one_edge_weight);
						}));
					}
					for (auto&& result : results) {
						result.get(); // to finish the above threads; since the amazon and movie threads return 1, but not return experiment_element value, amazon and movie threads do not need to be finished here
					}
					results.clear(); // future get value can only be called once for each thread result, must clear results here, otherwise you should not call the above future value again!
					clear_global_PLL_indexes("dblp_897782", one_edge_weight); // to save memory
				}
				if (1) {
					load_global_PLL_indexes("dblp_1697782", one_edge_weight);
					for (int ii = 1; ii <= split_num; ii++) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							return experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_3_" + to_string(ii) + ".csv", 1697782, T, b, tau, P_min, P_max,
								iteration_times / split_num, true, true, true, 0, 0, true, true, one_edge_weight);
						}));
					}
					for (auto&& result : results) {
						result.get(); // since V2 future values have been cleared above, it's safe to get all futures values in reults here
					}
					results.clear();
					clear_global_PLL_indexes("dblp_1697782", one_edge_weight);
				}
			}


			/*others*/
			if (1) {

				load_global_PLL_indexes("dblp_2497782", one_edge_weight);
				int split_num = 10;
				for (int ii = 1; ii <= split_num; ii++) {

					/*vary V*/
					if (1) {
						//results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
						//	experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_V_1_" + to_string(ii) + ".csv", 80, T, b, tau, P_min, P_max, iteration_times / split_num,
						//		true, true, true, true, true, true, true, one_edge_weight);
						//	return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
					}

					/*vary T*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_1_" + to_string(ii) + ".csv", V, 3, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_2_" + to_string(ii) + ".csv", V, 4, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_T_3_" + to_string(ii) + ".csv", V, 6, b, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
					}

					/*vary b*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_1_" + to_string(ii) + ".csv", V, T, 0.8, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_2_" + to_string(ii) + ".csv", V, T, 0.85, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_b_3_" + to_string(ii) + ".csv", V, T, 0.95, tau, P_min, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
					}

					/*vary tau*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_1_" + to_string(ii) + ".csv", V, T, b, 3, P_min, P_max, iteration_times / split_num,
								0, true, 0, 0, 0, 0, 0, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_2_" + to_string(ii) + ".csv", V, T, b, 5, P_min, P_max, iteration_times / split_num,
								0, true, 0, 0, 0, 0, 0, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_tau_3_" + to_string(ii) + ".csv", V, T, b, 7, P_min, P_max, iteration_times / split_num,
								0, true, 0, 0, 0, 0, 0, one_edge_weight);
							return 1; }));
					}

					/*vary P_min*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_1_" + to_string(ii) + ".csv", V, T, b, tau, 0.4, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_2_" + to_string(ii) + ".csv", V, T, b, tau, 0.6, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_min_3_" + to_string(ii) + ".csv", V, T, b, tau, 0.7, P_max, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
					}

					/*vary P_max*/
					if (1) {
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_1_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.7, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_2_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 0.8, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
						results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
							experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_P_max_3_" + to_string(ii) + ".csv", V, T, b, tau, P_min, 1, iteration_times / split_num,
								true, true, true, 0, 0, true, true, one_edge_weight);
							return 1; }));
					}

				}
				for (auto&& result : results) {
					result.get(); // wait for the below clear
				}
				results.clear();
				clear_global_PLL_indexes("dblp_2497782", one_edge_weight);


			}
			
		}		
	}

}
#pragma endregion experiments

#pragma region
void example_experiments() {

	/* only DUAL and GRETREE do not need PLL indexes */

	int pool_size = 10; 
	ThreadPool pool(pool_size); // use pool_size threads to do parallel computing
	std::vector< std::future<int> > results;

	/*one_edge_weight*/
	if (1) {
		bool one_edge_weight = true;
		/*amazon*/
		if (1) {
			string data_name = "amazon";
			load_global_PLL_indexes(data_name, one_edge_weight); // load the amazon hub labeling indexes, one_edge_weight is true means all edge costs are 1
			int iteration_times = 100; // a random experiment with 100 times
			int V = 548552, T = 5;
			double b = 0.9, tau = 1, P_min = 0.5, P_max = 0.9;

			/*the following is to split the 100 experiment into 10 parts, and then do these parts in parallel;
			
			for each part, call "experiment_element". The input values of "experiment_element" are as follows.

			data_name: "amazon", "dblp", or "movie". This is to choose which dataset to run.
			V: number of vertices.
			T: number of vertex groups.
			b: the threshold value.
			tau: the approximation parameter.
			P_min, P_max: the probability values as decribed in our paper.
			iteration_times: how many random experiments to run.
			use_ENSteiner, use_PrunedDPPP, etc: true is to use the algortihm, false is to not use.
			one_edge_weight: true is to set all edge costs to 1, false is to set edge costs to Jaccard distances.
			*/
			int split_num = 10;
			for (int ii = 1; ii <= split_num; ii++) {
				results.emplace_back(pool.enqueue([data_name, V, T, b, tau, P_min, P_max, iteration_times, ii, split_num, one_edge_weight] {
					experiment_element(data_name, "Exp_" + data_name + "_one_edge_weight_vary_base_" + to_string(ii) + ".csv", V, T, b, tau, P_min, P_max, iteration_times / split_num,
						true, true, true, 0, true, true, true, one_edge_weight); 
					return 1; }));
			}
		}

		for (auto&& result : results) {
			result.get(); // wait for all the above threads to finish
		}
		results.clear();
		clear_global_PLL_indexes("amazon", one_edge_weight); // clear the amazon hub labeling indexes
	}

}
#pragma endregion example_experiments


int main()
{
	auto begin = std::chrono::high_resolution_clock::now();

	/*the two values below are for #include <graph_hash_of_mixed_weighted.h>*/
	graph_hash_of_mixed_weighted_turn_on_value = 1e3;
	graph_hash_of_mixed_weighted_turn_off_value = 1e1;

	example_experiments();

	auto end = std::chrono::high_resolution_clock::now();
	double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s


	cout << "END    runningtime: " << runningtime << "s" << endl;
}
