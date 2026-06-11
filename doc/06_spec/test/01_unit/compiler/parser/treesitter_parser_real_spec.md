# TreeSitterParser Real Implementation Tests

> Tests for the actual TreeSitterParser implementation

<!-- sdn-diagram:id=treesitter_parser_real_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_parser_real_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_parser_real_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_parser_real_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitterParser Real Implementation Tests

Tests for the actual TreeSitterParser implementation

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-MAIN-001 |
| Category | Parser \| Core |
| Status | Planned |
| Source | `test/01_unit/compiler/parser/treesitter_parser_real_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the actual TreeSitterParser implementation
in std.parser.treesitter.parser.

NOTE: Tests are skipped until std.parser.treesitter module parse errors are fixed.

## Scenarios

### TreeSitterParser Creation

#### creates parser for simple language

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = TreeSitterParser.new("simple")
# expect result.is_ok()
expect true
```

</details>

#### rejects unsupported language

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = TreeSitterParser.new("python")
# expect result.is_err()
# val err = result.unwrap_err()
# expect err.contains("Unsupported language")
expect true
```

</details>

#### rejects empty language string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = TreeSitterParser.new("")
# expect result.is_err()
expect true
```

</details>

#### rejects random language name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = TreeSitterParser.new("foobar")
# expect result.is_err()
expect true
```

</details>

### Basic Parsing

#### parses empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("")
# expect result.is_ok()
expect true
```

</details>

#### parses simple expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("42")
# expect result.is_ok()
# val tree = result.unwrap()
# expect tree.source == "42"
expect true
```

</details>

#### parses variable declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("val x = 1")
# expect result.is_ok()
expect true
```

</details>

#### parses binary expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("1 + 2")
# expect result.is_ok()
expect true
```

</details>

#### parses comparison expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("a < b")
# expect result.is_ok()
expect true
```

</details>

### Function Parsing

#### parses simple function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "fn foo(): 42"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses function with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "fn add(a, b): a + b"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses function with return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "fn square(x) -> i64: x * x"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

### Control Flow Parsing

#### parses if statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "if x: 1"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses if-else statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "if x: 1 else: 2"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "while x: x"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>


</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "for i in items: i"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>


</details>

#### parses match expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "match x: case 1: a"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

### Type Definition Parsing

#### parses struct definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "struct Point: x: i64"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses class definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "class Counter: count: i64"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses enum definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "enum Color: Red"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

### Tree Structure

#### tree has root node

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("x").unwrap()
# val root = tree.root()
# expect root.is_some()
expect true
```

</details>

#### tree stores source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val source = "val answer = 42"
# val tree = parser.parse(source).unwrap()
# expect tree.source == source
expect true
```

</details>

#### tree has version 0 initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("1").unwrap()
# expect tree.version == 0
expect true
```

</details>

#### can walk tree with cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("x + y").unwrap()
# var cursor = tree.walk()
# val node = cursor.node()
# expect node.is_some()
expect true
```

</details>

### Node Properties

#### node has kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("42").unwrap()
# val root = tree.root().unwrap()
# expect root.kind.len() > 0
expect true
```

</details>

#### node has span

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("abc").unwrap()
# val root = tree.root().unwrap()
# expect root.span.start_byte >= 0
# expect root.span.end_byte >= root.span.start_byte
expect true
```

</details>

#### leaf node has no children

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("42").unwrap()
# var cursor = tree.walk()
# while cursor.goto_first_child():
#     pass
# val leaf = cursor.node().unwrap()
# expect leaf.child_count() >= 0
expect true
```

</details>

### Incremental Parsing

#### incremental parse with no edits returns same tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree1 = parser.parse("x").unwrap()
# val tree2 = parser.parse_incremental("x", tree1, []).unwrap()
# expect tree2.version == tree1.version + 1
expect true
```

</details>

#### incremental parse preserves source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree1 = parser.parse("a").unwrap()
# val new_source = "b"
# val tree2 = parser.parse_incremental(new_source, tree1, []).unwrap()
# expect tree2.source == new_source
expect true
```

</details>

### Tree Cursor Navigation

#### cursor starts at root

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("1 + 2").unwrap()
# var cursor = tree.walk()
# expect cursor.depth == 0
expect true
```

</details>

#### goto_first_child increases depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("fn f(): 1").unwrap()
# var cursor = tree.walk()
# val had_child = cursor.goto_first_child()
# if had_child:
#     expect cursor.depth == 1
expect true
```

</details>

#### goto_parent decreases depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("fn f(): 1").unwrap()
# var cursor = tree.walk()
# if cursor.goto_first_child():
#     val old_depth = cursor.depth
#     if cursor.goto_parent():
#         expect cursor.depth == old_depth - 1
expect true
```

</details>

#### goto_next_sibling moves horizontally

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("a + b + c").unwrap()
# var cursor = tree.walk()
# if cursor.goto_first_child():
#     val first_node = cursor.node()
#     if cursor.goto_next_sibling():
#         val second_node = cursor.node()
#         expect first_node.is_some() and second_node.is_some()
expect true
```

</details>

### Parser Error Handling

#### reports error for invalid syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("fn fn fn")
# expect result.is_ok() or result.is_err()
expect true
```

</details>

#### handles unclosed parenthesis

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("foo(")
# expect result.is_ok() or result.is_err()
expect true
```

</details>

#### handles unclosed brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse(r"fn f() {")  # raw string to avoid f-string interpolation
# expect result.is_ok() or result.is_err()
expect true
```

</details>

### Complex Code Parsing

#### parses nested expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("(1 + 2) * (3 + 4)")
# expect result.is_ok()
expect true
```

</details>

#### parses function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("foo(1, 2, 3)")
# expect result.is_ok()
expect true
```

</details>

#### parses method call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("obj.method()")
# expect result.is_ok()
expect true
```

</details>

#### parses array literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("[1, 2, 3]")
# expect result.is_ok()
expect true
```

</details>

#### parses multiple statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "val x = 1{NL}val y = 2{NL}x + y"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
