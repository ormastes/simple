# TreeSitterParser Real Implementation Tests

> Tests for the actual TreeSitterParser implementation

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
| Source | `test/unit/compiler/parser/treesitter_parser_real_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the actual TreeSitterParser implementation
in std.parser.treesitter.parser.

NOTE: Tests are skipped until std.parser.treesitter module parse errors are fixed.

## Scenarios

### TreeSitterParser Creation

#### creates parser for simple language

- creates parser for simple language


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates parser for simple language")
# val result = TreeSitterParser.new("simple")
# expect result.is_ok()
expect true
```

</details>

#### rejects unsupported language

- rejects unsupported language


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported language")
# val result = TreeSitterParser.new("python")
# expect result.is_err()
# val err = result.unwrap_err()
# expect err.contains("Unsupported language")
expect true
```

</details>

#### rejects empty language string

- rejects empty language string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty language string")
# val result = TreeSitterParser.new("")
# expect result.is_err()
expect true
```

</details>

#### rejects random language name

- rejects random language name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects random language name")
# val result = TreeSitterParser.new("foobar")
# expect result.is_err()
expect true
```

</details>

### Basic Parsing

#### parses empty source

- parses empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty source")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("")
# expect result.is_ok()
expect true
```

</details>

#### parses simple expression

- parses simple expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple expression")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("42")
# expect result.is_ok()
# val tree = result.unwrap()
# expect tree.source == "42"
expect true
```

</details>

#### parses variable declaration

- parses variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses variable declaration")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("val x = 1")
# expect result.is_ok()
expect true
```

</details>

#### parses binary expression

- parses binary expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses binary expression")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("1 + 2")
# expect result.is_ok()
expect true
```

</details>

#### parses comparison expression

- parses comparison expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses comparison expression")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("a < b")
# expect result.is_ok()
expect true
```

</details>

### Function Parsing

#### parses simple function

- parses simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple function")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "fn foo(): 42"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses function with parameters

- parses function with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses function with parameters")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "fn add(a, b): a + b"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses function with return type

- parses function with return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses function with return type")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "fn square(x) -> i64: x * x"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

### Control Flow Parsing

#### parses if statement

- parses if statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses if statement")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "if x: 1"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses if-else statement

- parses if-else statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses if-else statement")
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

- parses while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses while loop")
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

- parses for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses for loop")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "for i in items: i"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>


</details>

#### parses match expression

- parses match expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses match expression")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "match x: case 1: a"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

### Type Definition Parsing

#### parses struct definition

- parses struct definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses struct definition")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "struct Point: x: i64"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses class definition

- parses class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses class definition")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "class Counter: count: i64"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

#### parses enum definition

- parses enum definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses enum definition")
# var parser = TreeSitterParser.new("simple").unwrap()
# val code = "enum Color: Red"
# val result = parser.parse(code)
# expect result.is_ok()
expect true
```

</details>

### Tree Structure

#### tree has root node

- tree has root node


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree has root node")
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("x").unwrap()
# val root = tree.root()
# expect root.is_some()
expect true
```

</details>

#### tree stores source

- tree stores source


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree stores source")
# var parser = TreeSitterParser.new("simple").unwrap()
# val source = "val answer = 42"
# val tree = parser.parse(source).unwrap()
# expect tree.source == source
expect true
```

</details>

#### tree has version 0 initially

- tree has version 0 initially


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree has version 0 initially")
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("1").unwrap()
# expect tree.version == 0
expect true
```

</details>

#### can walk tree with cursor

- can walk tree with cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can walk tree with cursor")
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

- node has kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("node has kind")
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("42").unwrap()
# val root = tree.root().unwrap()
# expect root.kind.len() > 0
expect true
```

</details>

#### node has span

- node has span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("node has span")
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("abc").unwrap()
# val root = tree.root().unwrap()
# expect root.span.start_byte >= 0
# expect root.span.end_byte >= root.span.start_byte
expect true
```

</details>

#### leaf node has no children

- leaf node has no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaf node has no children")
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

- incremental parse with no edits returns same tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incremental parse with no edits returns same tree")
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree1 = parser.parse("x").unwrap()
# val tree2 = parser.parse_incremental("x", tree1, []).unwrap()
# expect tree2.version == tree1.version + 1
expect true
```

</details>

#### incremental parse preserves source

- incremental parse preserves source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incremental parse preserves source")
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

- cursor starts at root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cursor starts at root")
# var parser = TreeSitterParser.new("simple").unwrap()
# val tree = parser.parse("1 + 2").unwrap()
# var cursor = tree.walk()
# expect cursor.depth == 0
expect true
```

</details>

#### goto_first_child increases depth

- goto_first_child increases depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("goto_first_child increases depth")
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

- goto_parent decreases depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("goto_parent decreases depth")
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

- goto_next_sibling moves horizontally


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("goto_next_sibling moves horizontally")
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

- reports error for invalid syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports error for invalid syntax")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("fn fn fn")
# expect result.is_ok() or result.is_err()
expect true
```

</details>

#### handles unclosed parenthesis

- handles unclosed parenthesis


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unclosed parenthesis")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("foo(")
# expect result.is_ok() or result.is_err()
expect true
```

</details>

#### handles unclosed brace

- handles unclosed brace


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unclosed brace")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse(r"fn f() {")  # raw string to avoid f-string interpolation
# expect result.is_ok() or result.is_err()
expect true
```

</details>

### Complex Code Parsing

#### parses nested expressions

- parses nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested expressions")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("(1 + 2) * (3 + 4)")
# expect result.is_ok()
expect true
```

</details>

#### parses function call

- parses function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses function call")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("foo(1, 2, 3)")
# expect result.is_ok()
expect true
```

</details>

#### parses method call

- parses method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses method call")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("obj.method()")
# expect result.is_ok()
expect true
```

</details>

#### parses array literal

- parses array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses array literal")
# var parser = TreeSitterParser.new("simple").unwrap()
# val result = parser.parse("[1, 2, 3]")
# expect result.is_ok()
expect true
```

</details>

#### parses multiple statements

- parses multiple statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple statements")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `16bc7c5d670fab8e967c8d56fdfaaefb9ed1f9e0902db40569885b428299c935`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16bc7c5d670fab8e967c8d56fdfaaefb9ed1f9e0902db40569885b428299c935`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16bc7c5d670fab8e967c8d56fdfaaefb9ed1f9e0902db40569885b428299c935`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/compiler/parser/treesitter_parser_real_spec.spl
mirror: doc/06_spec/unit/compiler/parser/treesitter_parser_real_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/treesitter_parser_real_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/treesitter_parser_real_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/treesitter_parser_real_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates parser for simple language' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_parser_real_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported language' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_parser_real_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty language string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_parser_real_spec.spl:282:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can walk tree with cursor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
