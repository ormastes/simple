# TreeSitter Node API Guide

**Module:** `std.parser.treesitter_node`
**Status:** Stable (Features 1-2)
**Version:** 1.0

## Overview

The TreeSitter Node API provides a Simple-language wrapper around the TreeSitter C library's node operations. It enables:

1. **Position Tracking** - Query node locations in source code
2. **Tree Navigation** - Walk parse trees via parent/sibling relationships
3. **Node Properties** - Check node types, errors, and metadata

## Quick Start

```simple
use std.parser.treesitter_node.{Node, Point}

# Create a node from a TreeSitter handle
val node = Node(handle: node_handle)

# Get position information
val start = node.start_byte()        # i64: byte offset
val end_val = node.end_byte()        # i64: byte offset
val start_pt = node.start_point()    # Point: (row, column)
val end_pt = node.end_point()        # Point: (row, column)

# Navigate the tree
val parent = node.parent()           # Node? (nil if root)
val next = node.next_sibling()       # Node? (nil if last)
val prev = node.prev_sibling()       # Node? (nil if first)

# Query node properties
val kind = node.kind()               # text: "function_definition", etc.
val has_err = node.has_error()       # bool: true if errors present
```

## Data Types

### Node

Represents a node in a TreeSitter parse tree.

```simple
struct Node:
    handle: i64  # Opaque FFI handle to TreeSitter node
```

The `handle` is an internal identifier managed by the TreeSitter runtime. You typically don't create Node instances manually—they're returned by parser operations.

### Point

Represents a position in source code as (row, column).

```simple
struct Point:
    row: i64     # Zero-indexed line number
    column: i64  # Zero-indexed column number
```

Both row and column are 0-indexed, following TreeSitter conventions:
- First line: row = 0
- First column: column = 0

## Position Tracking Methods

### start_byte()

Get the start byte offset of a node.

```simple
fn start_byte() -> i64
```

**Returns:** Zero-indexed byte position where the node begins in the source.

**Example:**
```simple
val node = Node(handle: h)
val start = node.start_byte()
print "Node starts at byte {start}"
```

### end_byte()

Get the end byte offset of a node.

```simple
fn end_byte() -> i64
```

**Returns:** Zero-indexed byte position where the node ends in the source (exclusive).

**Example:**
```simple
val node = Node(handle: h)
val length = node.end_byte() - node.start_byte()
print "Node is {length} bytes long"
```

### start_point()

Get the start position as (row, column).

```simple
fn start_point() -> Point
```

**Returns:** Point with zero-indexed row and column.

**Example:**
```simple
val node = Node(handle: h)
val pt = node.start_point()
print "Node starts at line {pt.row + 1}, column {pt.column + 1}"
# Note: +1 for human-readable (1-indexed) display
```

### end_point()

Get the end position as (row, column).

```simple
fn end_point() -> Point
```

**Returns:** Point with zero-indexed row and column.

**Example:**
```simple
val node = Node(handle: h)
val start = node.start_point()
val end_pt = node.end_point()
if start.row == end_pt.row:
    print "Single-line node"
else:
    print "Multi-line node spanning {end_pt.row - start.row + 1} lines"
```

## Navigation Methods

All navigation methods return `Node?` (optional node) to handle edge cases:
- **nil** indicates no such node exists (root has no parent, last child has no next sibling, etc.)
- **Node** indicates a valid node was found

### parent()

Get the parent node.

```simple
fn parent() -> Node?
```

**Returns:**
- `Node` if parent exists
- `nil` if this is the root node

**Example:**
```simple
val node = Node(handle: h)
val parent = node.parent()
if parent != nil:
    print "Parent type: {parent.kind()}"
else:
    print "This is the root node"
```

### next_sibling()

Get the next sibling node.

```simple
fn next_sibling() -> Node?
```

**Returns:**
- `Node` if next sibling exists
- `nil` if this is the last child

**Example:**
```simple
val node = Node(handle: h)
var current = node
for _ in 0..100:  # Safety limit
    val next = current.next_sibling()
    if next == nil:
        break
    print "Sibling: {next.kind()}"
    current = next
```

### prev_sibling()

Get the previous sibling node.

```simple
fn prev_sibling() -> Node?
```

**Returns:**
- `Node` if previous sibling exists
- `nil` if this is the first child

**Example:**
```simple
val node = Node(handle: h)
var current = node
for _ in 0..100:  # Safety limit
    val prev = current.prev_sibling()
    if prev == nil:
        break
    print "Previous sibling: {prev.kind()}"
    current = prev
```

## Node Property Methods

### kind()

Get the node type string.

```simple
fn kind() -> text
```

**Returns:** Node type name like "function_definition", "identifier", "binary_expression", etc.

**Example:**
```simple
val node = Node(handle: h)
val k = node.kind()
if k == "function_definition":
    print "This is a function"
```

### has_error()

Check if the node or any descendant has parse errors.

```simple
fn has_error() -> bool
```

**Returns:** `true` if errors present, `false` otherwise.

**Example:**
```simple
val node = Node(handle: h)
if node.has_error():
    print "Parse error detected in this subtree"
```

### is_missing()

Check if the node was inserted by error recovery.

```simple
fn is_missing() -> bool
```

**Returns:** `true` if this node was synthesized by the parser to recover from an error.

### is_named()

Check if the node is "named" (not anonymous).

```simple
fn is_named() -> bool
```

Anonymous nodes are typically punctuation like `(`, `)`, `,`. Named nodes are semantic constructs.

### is_null()

Check if the node handle is null/invalid.

```simple
fn is_null() -> bool
```

**Returns:** `true` if the handle is 0 (invalid).

## Child Access Methods

### child_count()

Get total number of children (including anonymous nodes).

```simple
fn child_count() -> i64
```

### child()

Get child at index.

```simple
fn child(index: i64) -> Node?
```

**Returns:** `Node` if index is valid, `nil` otherwise.

**Example:**
```simple
val node = Node(handle: h)
val count = node.child_count()
for i in 0..count:
    val c = node.child(i)
    if c != nil:
        print "Child {i}: {c.kind()}"
```

### named_child_count()

Get number of named children (excludes anonymous nodes).

```simple
fn named_child_count() -> i64
```

### named_child()

Get named child at index.

```simple
fn named_child(index: i64) -> Node?
```

## Utility Functions

### node_is_valid()

Check if a node is valid (not nil and not null handle).

```simple
fn node_is_valid(node: Node?) -> bool
```

**Example:**
```simple
val parent = node.parent()
if node_is_valid(parent):
    print "Has valid parent"
```

### node_byte_range()

Get byte range as a tuple.

```simple
fn node_byte_range(node: Node) -> (i64, i64)
```

**Returns:** `(start_byte, end_byte)`

**Example:**
```simple
val range = node_byte_range(node)
val source_slice = source[range.0:range.1]
```

### node_line_range()

Get line range as a tuple.

```simple
fn node_line_range(node: Node) -> (i64, i64)
```

**Returns:** `(start_line, end_line)` (zero-indexed)

## Common Patterns

### Walking All Children

```simple
fn walk_children(node: Node):
    val count = node.child_count()
    for i in 0..count:
        val c = node.child(i)
        if c != nil:
            print "Child: {c.kind()}"
            walk_children(c)  # Recursive
```

### Walking Named Children Only

```simple
fn walk_named_children(node: Node):
    val count = node.named_child_count()
    for i in 0..count:
        val c = node.named_child(i)
        if c != nil:
            print "Named child: {c.kind()}"
```

### Walking All Siblings

```simple
fn walk_siblings(node: Node):
    # Go to first sibling
    var current = node
    for _ in 0..1000:
        val prev = current.prev_sibling()
        if prev == nil:
            break
        current = prev

    # Walk forward
    for _ in 0..1000:
        print "Sibling: {current.kind()}"
        val next = current.next_sibling()
        if next == nil:
            break
        current = next
```

### Finding Parent of Specific Type

```simple
fn find_parent_of_kind(node: Node, target_kind: text) -> Node?:
    var current = node
    for _ in 0..100:  # Max depth
        val parent = current.parent()
        if parent == nil:
            return nil
        if parent.kind() == target_kind:
            return parent
        current = parent
    nil
```

### Extracting Source Text

```simple
fn node_text(node: Node, source: text) -> text:
    val start = node.start_byte()
    val end_val = node.end_byte()
    source[start:end_val]
```

### Checking for Errors in Tree

```simple
fn has_errors_in_tree(root: Node) -> bool:
    if root.has_error():
        return true

    val count = root.child_count()
    for i in 0..count:
        val c = root.child(i)
        if c != nil and has_errors_in_tree(c):
            return true
    false
```

## Performance Considerations

1. **Handle Validity:** Always check if nodes are nil before using them.
2. **Loop Limits:** Use safety limits when walking unbounded structures (siblings, ancestors).
3. **Caching:** Cache frequently accessed node properties to avoid repeated FFI calls.
4. **Depth Limits:** Recursive tree walking should have depth limits to prevent stack overflow.

## Error Handling

### Invalid Handles

If a node handle is invalid (0), methods will return default values:
- `kind()` returns empty string
- `child_count()` returns 0
- Navigation methods return nil
- Position methods return 0 or Point(0, 0)

### Nil Nodes

Optional navigation methods return nil when:
- Root node's parent is requested
- Last child's next sibling is requested
- First child's previous sibling is requested
- Invalid child index is accessed

Always check for nil:

```simple
val parent = node.parent()
if parent == nil:
    print "No parent (root node)"
else:
    print "Parent: {parent.kind()}"
```

## Integration with Parser

The Node API is designed to work with TreeSitter parsers:

```simple
# (Pseudo-code - parser API to be implemented)
# use std.parser.treesitter_parser.{Parser}
#
# val parser = Parser.new("simple")
# val tree = parser.parse(source)
# val root = tree.root_node()
#
# # Now use Node API
# val start = root.start_point()
# print "Root starts at line {start.row}"
```

## FFI Reference

The Node API wraps these TreeSitter C functions:

**Position:**
- `rt_ts_node_start_byte(handle: i64) -> i64`
- `rt_ts_node_end_byte(handle: i64) -> i64`
- `rt_ts_node_start_point(handle: i64) -> (i64, i64)`
- `rt_ts_node_end_point(handle: i64) -> (i64, i64)`

**Navigation:**
- `rt_ts_node_parent(handle: i64) -> i64`
- `rt_ts_node_next_sibling(handle: i64) -> i64`
- `rt_ts_node_prev_sibling(handle: i64) -> i64`

**Properties:**
- `rt_ts_node_type(handle: i64) -> text`
- `rt_ts_node_has_error(handle: i64) -> bool`
- `rt_ts_node_is_missing(handle: i64) -> bool`
- `rt_ts_node_is_named(handle: i64) -> bool`
- `rt_ts_node_is_null(handle: i64) -> bool`

FFI spec: `src/app/ffi_gen/specs/treesitter.spl`

## See Also

- **Implementation Plan:** `doc/IMPLEMENTATION_PLAN_5_PHASE.md` (Phase 2.3)
- **Progress Tracking:** `doc/feature/treesitter_implementation.md`
- **FFI Spec:** `src/app/ffi_gen/specs/treesitter.spl`
- **TreeSitter C API:** https://tree-sitter.github.io/tree-sitter/using-parsers

## Changelog

### Version 1.0 (2026-02-14)
- Initial implementation of Features 1-2
- Position tracking: start_byte, end_byte, start_point, end_point
- Navigation: parent, next_sibling, prev_sibling
- Basic node operations: kind, child access, properties
- Utility functions: node_is_valid, node_byte_range, node_line_range
