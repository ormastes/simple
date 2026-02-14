# TreeSitter Integration Example

**Module:** `std.parser.treesitter_node`
**Audience:** Compiler developers, LSP implementers
**Last Updated:** 2026-02-14

## Overview

This guide shows practical examples of integrating the TreeSitter Node API into compiler and tooling code.

## Basic Usage Example

```simple
use std.parser.treesitter_node.{Node, Point, node_byte_range}

fn analyze_node(node: Node, source: text):
    """Analyze a TreeSitter node and print information."""

    # Get position information
    val start = node.start_byte()
    val end_val = node.end_byte()
    val start_pt = node.start_point()
    val end_pt = node.end_point()

    # Extract source text
    val text = source[start:end_val]

    # Display information
    print "Node: {node.kind()}"
    print "  Position: line {start_pt.row + 1}, col {start_pt.column + 1}"
    print "  Range: bytes {start}-{end_val}"
    print "  Text: {text}"

    # Check for errors
    if node.has_error():
        print "  ERROR: Parse error in this subtree"
```

## Walking a Parse Tree

### Depth-First Traversal

```simple
fn walk_tree_depth_first(node: Node, depth: i64):
    """Walk entire tree in depth-first order."""

    # Print current node
    val indent = " " * (depth * 2)
    print "{indent}{node.kind()}"

    # Visit children
    val count = node.child_count()
    for i in 0..count:
        val child = node.child(i)
        if child != nil:
            walk_tree_depth_first(child, depth + 1)
```

### Named Nodes Only

```simple
fn walk_named_nodes(node: Node, depth: i64):
    """Walk only named (semantic) nodes."""

    if node.is_named():
        val indent = " " * (depth * 2)
        print "{indent}{node.kind()}"

    val count = node.named_child_count()
    for i in 0..count:
        val child = node.named_child(i)
        if child != nil:
            walk_named_nodes(child, depth + 1)
```

## Finding Nodes

### Find Node at Position

```simple
fn find_node_at_position(root: Node, target_line: i64, target_col: i64) -> Node?:
    """Find the deepest node containing the given position."""

    # Check if position is in this node
    val start = root.start_point()
    val end_pt = root.end_point()

    # Check if position is before/after this node
    if target_line < start.row or target_line > end_pt.row:
        return nil

    # Check column bounds for single-line nodes
    if start.row == end_pt.row:
        if target_col < start.column or target_col >= end_pt.column:
            return nil

    # Position is in this node - check children
    var deepest = root
    val count = root.child_count()
    for i in 0..count:
        val child = root.child(i)
        if child != nil:
            val found = find_node_at_position(child, target_line, target_col)
            if found != nil:
                deepest = found

    deepest
```

### Find Parent of Type

```simple
fn find_parent_of_kind(node: Node, target_kind: text) -> Node?:
    """Walk up the tree to find parent of specific kind."""

    var current = node
    for _ in 0..100:  # Max depth limit
        val parent = current.parent()
        if parent == nil:
            return nil

        if parent.kind() == target_kind:
            return parent

        current = parent

    nil  # Not found within depth limit
```

### Find All Nodes of Type

```simple
fn find_all_of_kind(root: Node, target_kind: text) -> [Node]:
    """Find all nodes of a specific kind in the tree."""

    var results = []

    # Check current node
    if root.kind() == target_kind:
        results = results + [root]

    # Recursively check children
    val count = root.child_count()
    for i in 0..count:
        val child = root.child(i)
        if child != nil:
            val child_results = find_all_of_kind(child, target_kind)
            results = results + child_results

    results
```

## Error Handling

### Collecting Parse Errors

```simple
struct ErrorLocation:
    line: i64
    column: i64
    message: text

fn collect_errors(root: Node, source: text) -> [ErrorLocation]:
    """Collect all parse errors in the tree."""

    var errors = []

    if root.has_error():
        if root.is_missing():
            # Node was inserted by error recovery
            val start = root.start_point()
            val err = ErrorLocation(
                line: start.row + 1,
                column: start.column + 1,
                message: "Missing {root.kind()}"
            )
            errors = errors + [err]

        # Check children for errors
        val count = root.child_count()
        for i in 0..count:
            val child = root.child(i)
            if child != nil:
                val child_errors = collect_errors(child, source)
                errors = errors + child_errors

    errors
```

### Checking Subtree Health

```simple
fn is_subtree_valid(node: Node) -> bool:
    """Check if a subtree has no parse errors."""

    if node.has_error():
        return false

    if node.is_missing():
        return false

    # Check all children
    val count = node.child_count()
    for i in 0..count:
        val child = node.child(i)
        if child != nil:
            if not is_subtree_valid(child):
                return false

    true
```

## Source Text Extraction

### Extract Node Text

```simple
fn node_text(node: Node, source: text) -> text:
    """Extract source text for a node."""
    val range = node_byte_range(node)
    source[range.0:range.1]
```

### Extract with Context

```simple
fn node_text_with_context(node: Node, source: text, context_lines: i64) -> text:
    """Extract node text with surrounding context lines."""

    val start = node.start_point()
    val end_pt = node.end_point()

    # Find byte offset of context start
    var start_line = start.row - context_lines
    if start_line < 0:
        start_line = 0

    var end_line = end_pt.row + context_lines

    # Simple implementation: extract full source and filter
    # (Real implementation would use line index)
    val lines = source.split("\n")
    var result = ""
    for i in start_line..end_line + 1:
        if i >= 0 and i < lines.len():
            result = result + lines[i] + "\n"

    result
```

## LSP Integration Pattern

### Hover Information

```simple
fn get_hover_info(root: Node, source: text, line: i64, col: i64) -> text?:
    """Get hover information for LSP textDocument/hover."""

    val node = find_node_at_position(root, line, col)
    if node == nil:
        return nil

    # Build hover text
    val kind = node.kind()
    val text = node_text(node, source)
    val start = node.start_point()

    val info = "Type: {kind}\nPosition: line {start.row + 1}, col {start.column + 1}\nText: {text}"
    info
```

### Go to Definition

```simple
fn find_definition(root: Node, source: text, line: i64, col: i64) -> Point?:
    """Find definition location for LSP textDocument/definition."""

    val node = find_node_at_position(root, line, col)
    if node == nil:
        return nil

    # Check if this is an identifier
    if node.kind() != "identifier":
        return nil

    val name = node_text(node, source)

    # Find declaration (simplified)
    val decl = find_declaration(root, name)
    if decl != nil:
        return decl.start_point()

    nil
```

## Syntax Highlighting

### Token Classification

```simple
enum TokenType:
    Keyword
    Identifier
    String
    Number
    Comment
    Operator

fn classify_token(node: Node) -> TokenType:
    """Classify a node for syntax highlighting."""

    val kind = node.kind()

    if kind == "keyword":
        return TokenType.Keyword
    elif kind == "identifier":
        return TokenType.Identifier
    elif kind == "string_literal":
        return TokenType.String
    elif kind == "number_literal":
        return TokenType.Number
    elif kind == "comment":
        return TokenType.Comment
    else:
        return TokenType.Identifier  # Default
```

### Highlighting Ranges

```simple
struct HighlightRange:
    start_line: i64
    start_col: i64
    end_line: i64
    end_col: i64
    token_type: TokenType

fn collect_highlights(root: Node) -> [HighlightRange]:
    """Collect all syntax highlight ranges."""

    var highlights = []

    if root.is_named():
        val token_type = classify_token(root)
        val start = root.start_point()
        val end_pt = root.end_point()

        val range = HighlightRange(
            start_line: start.row,
            start_col: start.column,
            end_line: end_pt.row,
            end_col: end_pt.column,
            token_type: token_type
        )
        highlights = highlights + [range]

    # Process children
    val count = root.child_count()
    for i in 0..count:
        val child = root.child(i)
        if child != nil:
            val child_highlights = collect_highlights(child)
            highlights = highlights + child_highlights

    highlights
```

## Performance Optimization

### Caching Node Properties

```simple
struct NodeCache:
    handle: i64
    kind: text
    start_byte: i64
    end_byte: i64
    start_point: Point
    end_point: Point

fn cache_node(node: Node) -> NodeCache:
    """Cache frequently accessed node properties."""
    NodeCache(
        handle: node.handle,
        kind: node.kind(),
        start_byte: node.start_byte(),
        end_byte: node.end_byte(),
        start_point: node.start_point(),
        end_point: node.end_point()
    )
```

### Lazy Child Access

```simple
fn lazy_walk(root: Node, visitor: fn(Node) -> bool):
    """Walk tree with early exit support."""

    # Visit current node
    if not visitor(root):
        return  # Visitor returned false, stop walking

    # Visit children
    val count = root.child_count()
    for i in 0..count:
        val child = root.child(i)
        if child != nil:
            lazy_walk(child, visitor)
```

## Testing Pattern

### Mock Node Creation

```simple
fn create_test_node() -> Node:
    """Create a mock node for testing (handle = 1)."""
    Node(handle: 1)
```

### Position Testing

```simple
fn test_position_tracking():
    """Test position tracking methods."""

    val node = create_test_node()

    # Test byte positions
    val start = node.start_byte()
    val end_val = node.end_byte()
    assert start >= 0
    assert end_val >= start

    # Test point positions
    val start_pt = node.start_point()
    val end_pt = node.end_point()
    assert start_pt.row >= 0
    assert start_pt.column >= 0
```

## Best Practices

### 1. Always Check for nil

```simple
# GOOD
val parent = node.parent()
if parent != nil:
    print parent.kind()

# BAD - can crash if parent is nil
val parent = node.parent()
print parent.kind()  # ERROR if nil
```

### 2. Use Loop Limits

```simple
# GOOD
var current = node
for _ in 0..100:  # Safety limit
    val next = current.next_sibling()
    if next == nil:
        break
    current = next

# BAD - can infinite loop
var current = node
while true:
    val next = current.next_sibling()
    if next == nil:
        break
    current = next
```

### 3. Cache Expensive Operations

```simple
# GOOD - cache child count
val count = node.child_count()
for i in 0..count:
    val child = node.child(i)
    # ...

# BAD - recomputes child_count every iteration
for i in 0..node.child_count():
    val child = node.child(i)
    # ...
```

### 4. Use Utility Functions

```simple
# GOOD
val range = node_byte_range(node)
val text = source[range.0:range.1]

# ALSO GOOD but more verbose
val start = node.start_byte()
val end_val = node.end_byte()
val text = source[start:end_val]
```

## Common Pitfalls

### 1. Zero-Based Indexing

```simple
# TreeSitter uses 0-based indexing
val pt = node.start_point()
print "Line {pt.row + 1}"  # Add 1 for human-readable display
```

### 2. Exclusive End Positions

```simple
# end_byte is EXCLUSIVE
val start = node.start_byte()
val end_val = node.end_byte()
val length = end_val - start  # Correct
val text = source[start:end_val]  # Correct (Python-style slice)
```

### 3. Handle Lifetime

```simple
# Handles are valid only while the tree exists
# Don't store handles across parse operations
```

## See Also

- **API Reference:** `doc/guide/treesitter_node_api.md`
- **Progress Tracking:** `doc/feature/treesitter_implementation.md`
- **Implementation Plan:** `doc/IMPLEMENTATION_PLAN_5_PHASE.md` (Phase 2.3)
- **FFI Spec:** `src/app/ffi_gen/specs/treesitter.spl`

---

**Last Updated:** 2026-02-14
**Version:** 1.0
