# Tree-Sitter Integration Guide

The Simple language includes a tree-sitter grammar and Node API for incremental parsing, syntax highlighting, and editor integration.

---

## Status

- Grammar: 40 tokens, 30 rules, 6 LSP query files -- verified complete
- Node API: stable (module `std.parser.treesitter_node`)
- Runtime integration: pending (module loading blocked)

---

## Node API

### Quick Start

```simple
use std.parser.treesitter_node.{Node, Point, node_byte_range}

val node = Node(handle: node_handle)

# Position information
val start = node.start_byte()        # i64: byte offset
val end_val = node.end_byte()        # i64: byte offset (exclusive)
val start_pt = node.start_point()    # Point: (row, column), zero-indexed
val end_pt = node.end_point()        # Point: (row, column), zero-indexed

# Tree navigation
val parent = node.parent()           # Node? (nil if root)
val next = node.next_sibling()       # Node? (nil if last)
val prev = node.prev_sibling()       # Node? (nil if first)

# Properties
val kind = node.kind()               # text: "function_definition", etc.
val has_err = node.has_error()       # bool: error in subtree
val missing = node.is_missing()      # bool: inserted by error recovery
val named = node.is_named()          # bool: semantic (not punctuation)
```

### Data Types

**Node**: Wraps a tree-sitter node handle.
```simple
struct Node:
    handle: i64  # Opaque FFI handle
```

**Point**: Zero-indexed position in source code.
```simple
struct Point:
    row: i64     # Zero-indexed line number
    column: i64  # Zero-indexed column number
```

### Child Access

```simple
val count = node.child_count()           # Total children (including anonymous)
val child = node.child(i)               # Node? at index
val named_count = node.named_child_count()  # Named children only
val named = node.named_child(i)          # Named child at index
```

### Utility Functions

```simple
fn node_is_valid(node: Node?) -> bool    # Not nil and not null handle
fn node_byte_range(node: Node) -> (i64, i64)  # (start_byte, end_byte)
fn node_line_range(node: Node) -> (i64, i64)  # (start_line, end_line)
```

---

## Common Patterns

### Walking a Parse Tree

```simple
fn walk_tree(node: Node, depth: i64):
    val indent = " " * (depth * 2)
    print "{indent}{node.kind()}"
    val count = node.child_count()
    for i in 0..count:
        val child = node.child(i)
        if child != nil:
            walk_tree(child, depth + 1)
```

### Finding Node at Position

```simple
fn find_node_at_position(root: Node, target_line: i64, target_col: i64) -> Node?:
    val start = root.start_point()
    val end_pt = root.end_point()
    if target_line < start.row or target_line > end_pt.row:
        return nil
    if start.row == end_pt.row:
        if target_col < start.column or target_col >= end_pt.column:
            return nil
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

### Finding Parent of Type

```simple
fn find_parent_of_kind(node: Node, target_kind: text) -> Node?:
    var current = node
    for _ in 0..100:  # Safety limit
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
    val range = node_byte_range(node)
    source[range.0:range.1]
```

### Collecting Parse Errors

```simple
fn collect_errors(root: Node, source: text) -> [ErrorLocation]:
    var errors = []
    if root.has_error():
        if root.is_missing():
            val start = root.start_point()
            errors = errors + [ErrorLocation(
                line: start.row + 1,
                column: start.column + 1,
                message: "Missing {root.kind()}"
            )]
        val count = root.child_count()
        for i in 0..count:
            val child = root.child(i)
            if child != nil:
                errors = errors + collect_errors(child, source)
    errors
```

---

## Best Practices

1. **Always check for nil** -- Navigation methods return `Node?`
   ```simple
   val parent = node.parent()
   if parent != nil:
       print parent.kind()
   ```

2. **Use loop limits** -- Prevent infinite loops when walking siblings or ancestors
   ```simple
   for _ in 0..100:  # Safety limit
       val next = current.next_sibling()
       if next == nil: break
       current = next
   ```

3. **Cache child count** -- Avoid recomputing in loop conditions
   ```simple
   val count = node.child_count()
   for i in 0..count:
       val child = node.child(i)
   ```

4. **Zero-based indexing** -- Add 1 for display
   ```simple
   val pt = node.start_point()
   print "Line {pt.row + 1}"
   ```

5. **Exclusive end positions** -- `end_byte()` is exclusive
   ```simple
   val length = node.end_byte() - node.start_byte()
   val text = source[node.start_byte():node.end_byte()]
   ```

---

## Performance Targets

| Metric | Target |
|--------|--------|
| Small file (100 lines) | < 5 ms |
| Medium file (1000 lines) | < 20 ms |
| Large file (10K lines) | < 100 ms |
| Incremental parse | < 5 ms |
| Query execution | < 10 ms |

---

## Grammar Components

- **Tokens**: 40 (keywords, operators, literals, punctuation)
- **Rules**: 30 (declarations, expressions, statements, patterns)
- **Query Files**: 6 (highlights, locals, folds, indents, injections, textobjects)
- **Error Recovery**: 7 strategies
- **Verification**: `scripts/verify_treesitter_grammar.sh`

Supported constructs: val/var declarations, fn/lambdas, generics (`<>`), AOP keywords, contract keywords, BDD keywords.

---

## Source Code

- **Grammar/API**: `src/lib/std/src/parser/treesitter/`
- **Tests**: `test/lib/std/unit/parser/treesitter/grammar_simple_spec.spl`
- **FFI spec**: `src/app/ffi_gen/specs/treesitter.spl`
- **Verification**: `scripts/verify_treesitter_grammar.sh`
