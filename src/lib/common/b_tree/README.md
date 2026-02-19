# B-Tree Implementation Modules

This directory contains the refactored B-tree implementation, split from the original 1,847-line `b_tree_utils.spl` file into 8 focused modules.

## Module Structure

### Core Modules

#### `types.spl` (237 lines)
**Purpose:** Core data structures and property accessors

**Contains:**
- Node and tree tuple structures
- Creation functions (`create_node`, `create_btree`)
- Property getters (`node_keys`, `tree_root`, etc.)
- Property setters (immutable updates)
- Capacity checking (`is_full`, `is_minimal`, `can_donate`)
- List helper functions

**Key Types:**
- `BTreeNode`: `(keys, children, is_leaf, n, t)`
- `BTree`: `(root, t, height)`

#### `search.spl` (106 lines)
**Purpose:** Key search and tree search operations

**Contains:**
- `find_key_index`: Find position of key in node
- `find_key`: Check if key exists in node
- `key_at_index`: Get key at specific index
- `search_node`: Recursive search in subtrees
- `btree_search`: Main search API

#### `split.spl` (141 lines)
**Purpose:** Node splitting during insertion

**Contains:**
- `split_child`: Split full child node
  - Creates new sibling
  - Moves keys and children
  - Promotes middle key to parent
  - Updates parent's children list

#### `insert.spl` (160 lines)
**Purpose:** Key insertion operations

**Contains:**
- `insert_non_full`: Insert into non-full node
- `btree_insert`: Main insertion API
  - Handles root splitting
  - Grows tree height when needed

**Dependencies:** `types`, `search`, `split`

#### `delete.spl` (526 lines)
**Purpose:** Key deletion operations

**Contains:**
- `get_predecessor`: Find largest key in left subtree
- `get_successor`: Find smallest key in right subtree
- `remove_from_leaf`: Remove key from leaf node
- `borrow_from_prev`: Borrow key from previous sibling
- `borrow_from_next`: Borrow key from next sibling
- `merge_nodes`: Merge child with sibling
- `fill_child`: Fill minimal child before deletion
- `delete_from_node`: Main deletion logic
- `btree_delete`: Delete API with root shrinking

**Dependencies:** `types`, `search`

#### `traverse.spl` (78 lines)
**Purpose:** Tree traversal algorithms

**Contains:**
- `inorder_node`: Recursive inorder traversal
- `inorder_traversal`: Main inorder API (sorted order)
- `keys_at_level`: Get keys at specific depth
- `level_order_traversal`: BFS traversal

**Dependencies:** `types`

#### `statistics.spl` (272 lines)
**Purpose:** Tree metrics and structural validation

**Contains:**
- Min/max finding (`btree_min`, `btree_max`)
- Size and counting (`btree_size`, `count_nodes`)
- Height calculation (`btree_height`)
- Validation functions:
  - `is_valid_key_count`: Check key count constraints
  - `are_keys_sorted`: Verify sorted order
  - `validate_node`: Recursive validation
  - `is_valid_btree`: Main validation API

**Dependencies:** `types`

#### `utilities.spl` (427 lines)
**Purpose:** Advanced operations and queries

**Contains:**
- Metrics: `get_fill_factor`, `avg_keys_per_node`
- Range queries: `range_query`, `keys_greater_than`, `keys_less_than`
- Bulk operations: `bulk_load`, `btree_from_list`
- Set operations: `btree_union`, `btree_intersection`, `btree_difference`
- Advanced queries: `find_closest`, `k_smallest`, `k_largest`, `get_median`
- Comparison: `btree_equals`, `is_subset`
- Inspection: `get_node_at_path`, `get_level_keys`
- Visualization: `print_tree`, `print_node_helper`
- Utility: `is_empty`, `clear_tree`, `contains`

**Dependencies:** `types`, `search`, `insert`, `traverse`, `statistics`

## Facade Pattern

The main file `src/std/b_tree_utils.spl` acts as a facade:
- Imports all submodules
- Re-exports all functions with `export *`
- Maintains backward compatibility
- Provides documentation and overview

## Design Principles

### Immutability
All operations return new structures rather than mutating in place:
```simple
val new_node = node_set_keys(node, updated_keys)
val new_tree = tree_set_root(tree, updated_root)
```

### Tuple-Based Structures
Uses tuples instead of classes for compatibility with runtime limitations:
```simple
# Node: (keys, children, is_leaf, n, t)
val node = ([], [], true, 0, 3)

# Tree: (root, t, height)
val tree = (root_node, 3, 0)
```

### No Runtime Limitations
- No generics (uses concrete types)
- No try/catch (uses nil for errors)
- No chained methods (intermediate variables)
- Pure functions with explicit returns

### Module Organization
- Each module handles one aspect of B-tree operations
- Clear separation of concerns
- Minimal cross-module dependencies
- Easy to understand and maintain

## Usage

Import the facade file as before:
```simple
mod std.b_tree_utils

val tree = create_btree(3)
tree = btree_insert(tree, 42)
val found = btree_search(tree, 42)
```

Or import specific modules:
```simple
mod b_tree.types
mod b_tree.insert

val tree = create_btree(3)
tree = btree_insert(tree, 42)
```

## Testing

All existing tests should pass without modification since the facade maintains full backward compatibility.

## Performance

No performance impact - the refactoring only reorganizes code into modules. All algorithms remain identical.

## File Sizes

| Module | Lines | Focus |
|--------|-------|-------|
| types.spl | 237 | Data structures |
| search.spl | 106 | Key search |
| split.spl | 141 | Node splitting |
| insert.spl | 160 | Insertion |
| delete.spl | 526 | Deletion |
| traverse.spl | 78 | Traversals |
| statistics.spl | 272 | Metrics & validation |
| utilities.spl | 427 | Advanced operations |
| **Total** | **1,947** | **(+100 lines for module headers)** |

Original file: 1,847 lines

## Refactoring Date

February 12, 2026

## References

- Original file: `src/std/b_tree_utils.spl`
- Facade pattern follows: `numerical_methods_utils.spl`, `json_parser_utils.spl`, `graph_utils.spl`, `gzip_utils.spl`
