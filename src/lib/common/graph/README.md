# Graph Algorithms Module

This directory contains the refactored graph algorithms module, split from the original 2,068-line `graph_utils.spl` file into 9 focused modules.

## Module Structure

### 1. `types.spl` (~330 lines)
**Purpose:** Core graph type definitions and construction operations

**Contents:**
- Graph representation (tuple-based with adjacency list)
- Graph constructors: `graph_new`, `graph_with_vertices`
- Type checking: `graph_is_directed`, `graph_is_weighted`
- Vertex/edge operations: `graph_add_vertex`, `graph_add_edge`, `graph_remove_vertex`, `graph_remove_edge`
- Graph conversions: `graph_to_matrix`, `graph_from_matrix`, `graph_to_edge_list`, `graph_from_edge_list`
- Neighbor operations: `graph_neighbors`

### 2. `traversal.spl` (~330 lines)
**Purpose:** Breadth-first and depth-first search implementations

**Contents:**
- DFS traversal: `graph_dfs`, `graph_dfs_with_order`, `graph_dfs_all`
- BFS traversal: `graph_bfs`, `graph_bfs_distances`, `graph_bfs_shortest_path`
- Topological sort: `graph_topological_sort`, `graph_topological_sort_kahn`
- Cycle detection helper: `graph_has_cycle_directed`

### 3. `shortest_path.spl` (~230 lines)
**Purpose:** Single-source and all-pairs shortest path algorithms

**Contents:**
- Dijkstra's algorithm: `graph_dijkstra`, `graph_dijkstra_with_paths`
- Path reconstruction: `graph_reconstruct_path`
- Bellman-Ford algorithm: `graph_bellman_ford` (handles negative weights)
- Floyd-Warshall algorithm: `graph_floyd_warshall` (all-pairs)

### 4. `spanning_tree.spl` (~140 lines)
**Purpose:** Minimum spanning tree algorithms

**Contents:**
- Kruskal's algorithm: `graph_kruskal` (union-find based)
- Prim's algorithm: `graph_prim` (greedy approach)

### 5. `flow.spl` (~60 lines)
**Purpose:** Maximum flow and minimum cut algorithms

**Contents:**
- Minimum cut: `graph_min_cut_bfs`
- Path checking: `graph_has_path`
- Edge weight utilities: `graph_edge_weight`

### 6. `matching.spl` (~55 lines)
**Purpose:** Graph matching and bipartite algorithms

**Contents:**
- Bipartite checking: `graph_is_bipartite`

### 7. `strongly_connected.spl` (~130 lines)
**Purpose:** Strongly connected components algorithms

**Contents:**
- Connected components: `graph_connected_components` (undirected)
- Connectivity checking: `graph_is_connected`
- Strongly connected components: `graph_strongly_connected_components` (Kosaraju)
- Graph reversal: `graph_reverse`

### 8. `coloring.spl` (~60 lines)
**Purpose:** Graph coloring algorithms

**Contents:**
- Greedy coloring: `graph_greedy_coloring`
- Chromatic number: `graph_chromatic_number`

### 9. `utilities.spl` (~730 lines)
**Purpose:** Common operations, metrics, properties, and transformations

**Contents:**
- Degree operations: `graph_degree`, `graph_in_degree`, `graph_out_degree`
- Cycle detection: `graph_has_cycle_undirected`, `graph_has_cycle_directed`, `graph_is_cyclic`
- Graph properties: `graph_is_tree`, `graph_is_dag`, `graph_is_regular`, `graph_is_simple`, `graph_sources`, `graph_sinks`, `graph_density`, `graph_isolated_vertices`
- Graph metrics: `graph_avg_degree`, `graph_max_degree_vertex`, `graph_min_degree_vertex`, `graph_diameter`, `graph_radius`, `graph_eccentricity`, `graph_center`, `graph_periphery`, `graph_total_weight`
- Special graph generators: `graph_complete`, `graph_cycle`, `graph_path`, `graph_star`, `graph_wheel`
- Graph transformations: `graph_complement`, `graph_induced_subgraph`, `graph_union`
- Bridges and articulation points: `graph_find_bridges`, `graph_find_articulation_points`
- Advanced paths: `graph_all_paths`, `graph_count_paths`, `graph_longest_path_dag`
- Comparison: `graph_same_size`, `graph_degree_sequence`
- Eulerian properties: `graph_has_eulerian_path`, `graph_has_eulerian_circuit`
- Clustering: `graph_count_triangles`, `graph_clustering_coefficient`, `graph_avg_clustering_coefficient`
- Utilities: `graph_print`, `graph_clone`, `graph_has_edge`, `graph_filter_by_weight`

## Data Structures

### Graph Representation
```simple
Graph: (directed: bool, weighted: bool, num_vertices: i64, edges: list, adj_list: map)
Edge: (from: i64, to: i64, weight: f64)
AdjList: map<i64, list<(to: i64, weight: f64)>>
```

Graphs are represented as tuples with:
- `directed` (bool): Whether the graph is directed
- `weighted` (bool): Whether edges have weights
- `num_vertices` (i64): Number of vertices
- `edges` (list): List of all edges as tuples (from, to, weight)
- `adj_list` (map): Adjacency list mapping vertex IDs to neighbor lists

## Usage

### Importing

The facade pattern ensures backward compatibility. All original imports still work:

```simple
# Import all graph functions (recommended)
mod graph_utils

# Use any function
var g = graph_new(false, false)
g = graph_add_edge(g, 0, 1, 1.0)
var visited = graph_dfs(g, 0)
```

You can also import specific modules if needed:

```simple
# Import specific module
mod graph.types
mod graph.traversal

var g = graph_new(false, false)
var visited = graph_bfs(g, 0)
```

### Example: Creating and Traversing a Graph

```simple
mod graph_utils

# Create an undirected, unweighted graph
var g = graph_new(false, false)

# Add edges
g = graph_add_edge_unweighted(g, 0, 1)
g = graph_add_edge_unweighted(g, 0, 2)
g = graph_add_edge_unweighted(g, 1, 3)
g = graph_add_edge_unweighted(g, 2, 3)

# Traverse using DFS
var dfs_result = graph_dfs(g, 0)
print dfs_result  # [0, 2, 3, 1] (order may vary)

# Traverse using BFS
var bfs_result = graph_bfs(g, 0)
print bfs_result  # [0, 1, 2, 3]
```

### Example: Shortest Path with Dijkstra

```simple
mod graph_utils

# Create a weighted directed graph
var g = graph_new(true, true)
g = graph_add_edge(g, 0, 1, 4.0)
g = graph_add_edge(g, 0, 2, 1.0)
g = graph_add_edge(g, 2, 1, 2.0)
g = graph_add_edge(g, 1, 3, 1.0)
g = graph_add_edge(g, 2, 3, 5.0)

# Find shortest paths from vertex 0
var distances = graph_dijkstra(g, 0)
print distances.get(3)  # 4.0 (path: 0 -> 2 -> 1 -> 3)
```

### Example: Minimum Spanning Tree

```simple
mod graph_utils

# Create a weighted undirected graph
var g = graph_new(false, true)
g = graph_add_edge(g, 0, 1, 4.0)
g = graph_add_edge(g, 0, 2, 8.0)
g = graph_add_edge(g, 1, 2, 11.0)
g = graph_add_edge(g, 1, 3, 8.0)
g = graph_add_edge(g, 2, 3, 7.0)

# Find MST using Kruskal's algorithm
var mst = graph_kruskal(g)
print mst  # List of edges in MST
```

## Design Patterns

### Facade Pattern
The `graph_utils.spl` file serves as a facade that re-exports all functions from the submodules. This ensures:
- **Backward compatibility:** Existing code continues to work
- **Clean organization:** Implementation is split into logical modules
- **Easy maintenance:** Changes are isolated to specific modules

### Module Dependencies
```
graph_utils.spl (facade)
├── graph.types (no dependencies)
├── graph.traversal (depends on types)
├── graph.shortest_path (depends on types)
├── graph.spanning_tree (depends on types)
├── graph.flow (depends on types, traversal)
├── graph.matching (depends on types)
├── graph.strongly_connected (depends on types, traversal)
├── graph.coloring (depends on types)
└── graph.utilities (depends on types, traversal, strongly_connected)
```

## Algorithm Complexity

### Traversal
- **DFS:** O(V + E) time, O(V) space
- **BFS:** O(V + E) time, O(V) space
- **Topological Sort:** O(V + E) time

### Shortest Path
- **Dijkstra:** O(V²) time (with simple array), O(V) space
- **Bellman-Ford:** O(VE) time, O(V) space
- **Floyd-Warshall:** O(V³) time, O(V²) space

### Spanning Tree
- **Kruskal:** O(E log E) time (sorting), O(V) space
- **Prim:** O(V²) time (with simple array), O(V) space

### Graph Properties
- **Cycle detection:** O(V + E) time
- **Bipartite check:** O(V + E) time
- **Strongly connected components:** O(V + E) time

## Migration Guide

### From Original File
If you were importing the original monolithic file:

```simple
# Before refactoring
mod graph_utils
var g = graph_new(false, false)
var visited = graph_dfs(g, 0)
```

**No changes needed!** The facade pattern ensures the same API:

```simple
# After refactoring (same code)
mod graph_utils
var g = graph_new(false, false)
var visited = graph_dfs(g, 0)
```

### Selective Imports
If you only need specific functionality, you can import individual modules:

```simple
# Only need graph construction and DFS
mod graph.types
mod graph.traversal

var g = graph_new(false, false)
var visited = graph_dfs(g, 0)
```

## Testing

All graph algorithms have comprehensive tests in `/test/std/graph_utils_spec.spl`. Run tests with:

```bash
bin/simple test test/std/graph_utils_spec.spl
```

## Original File

The original 2,068-line file is backed up at:
```
src/lib/common/graph/graph_utils.spl.backup
```

## Refactoring History

- **Date:** 2026-02-12
- **Original size:** 2,068 lines
- **Refactored into:** 9 modules (~2,065 lines total)
- **Pattern:** Facade with `export *`
- **Compatibility:** 100% backward compatible
