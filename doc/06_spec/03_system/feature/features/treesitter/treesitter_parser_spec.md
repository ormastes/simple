# TreeSitter Parser Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Parser Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-PARSER-001 to #TS-PARSER-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/features/treesitter/treesitter_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use std.spec.step

use std.parser.treesitter.{TreeSitterParser, Tree, Node}

val parser = TreeSitterParser.new("simple")?
val tree = parser.parse(source)?
val root = tree.root()?
```

## Scenarios

### TreeSitter Parser Creation

#### creates parser for Simple language

- creates parser for Simple language


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates parser for Simple language")
val result = TreeSitterParser.new("simple")
expect result.ok.?
```

</details>

#### rejects unsupported languages

- rejects unsupported languages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unsupported languages")
val result = TreeSitterParser.new("unknown_language")
expect result.err.?
```

</details>

#### creates parser with grammar loaded

- creates parser with grammar loaded


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates parser with grammar loaded")
val parser = TreeSitterParser.new("simple").unwrap()
# Parser should have grammar rules
expect true  # Parser created successfully
```

</details>

### TreeSitter Basic Parsing

#### simple expressions

#### parses integer literal

- parses integer literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses integer literal")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("42")
expect tree.ok.?
```

</details>

#### parses variable declaration

- parses variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses variable declaration")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42")
expect tree.ok.?
```

</details>

#### parses binary expression

- parses binary expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses binary expression")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 1 + 2")
expect tree.ok.?
```

</details>

#### function definitions

#### parses simple function

- parses simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple function")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn add(a, b):\n    a + b"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

#### parses function with return type

- parses function with return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses function with return type")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn get_value() -> i64:\n    42"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

#### parses function with parameters

- parses function with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses function with parameters")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn greet(name: text) -> text:\n    name"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

#### control flow

#### parses if statement

- parses if statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses if statement")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "if x > 0:\n    y = 1"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- parses while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses while loop")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "while x < 10:\n    x = x + 1"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>


</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- parses for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses for loop")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "for i in range(10):\n    sum = sum + i"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>


</details>

### TreeSitter Tree Structure

#### root node

#### has root node after parsing

- has root node after parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has root node after parsing")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root()
expect root.?
```

</details>

#### root node is module type

- root node is module type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("root node is module type")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.kind == "module"
```

</details>

#### child nodes

#### function has children

- function has children


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function has children")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn test():\n    42"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

#### node spans

#### nodes have valid spans

- nodes have valid spans


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nodes have valid spans")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.?
expect tree.source.len() > 0
```

</details>

### TreeSitter Node Types

#### identifies function definition

- identifies function definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies function definition")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn test():\n    42"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

#### identifies variable declaration

- identifies variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies variable declaration")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

#### identifies struct definition

- identifies struct definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies struct definition")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "struct Point:\n    x: i64\n    y: i64"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

### TreeSitter Multi-Statement Parsing

#### parses multiple declarations

- parses multiple declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple declarations")
var parser = TreeSitterParser.new("simple").unwrap()
val source = """val x = 1
```

</details>

#### parses mixed declarations

- parses mixed declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mixed declarations")
var parser = TreeSitterParser.new("simple").unwrap()
val source = """val x = 42
```

</details>

### TreeSitter Complex Expression Parsing

#### parses nested arithmetic

- parses nested arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested arithmetic")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = ((1 + 2) * 3)")
expect tree.ok.?
```

</details>

#### parses method chain

- parses method chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses method chain")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = obj.method1().method2()")
expect tree.ok.?
```

</details>

#### parses array literal

- parses array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses array literal")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val arr = [1, 2, 3]")
expect tree.ok.?
```

</details>

#### parses dictionary literal

- parses dictionary literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses dictionary literal")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val d = {\"key\": \"value\"}")
expect tree.ok.?
```

</details>

#### parses lambda expression

- parses lambda expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses lambda expression")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse(r"val f = \x: x + 1")
expect tree.ok.?
```

</details>

### TreeSitter Source Information

#### preserves source text

- preserves source text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves source text")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "val x = 42"
val tree = parser.parse(source).unwrap()
expect tree.source == source
```

</details>

#### tracks line numbers

- tracks line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks line numbers")
var parser = TreeSitterParser.new("simple").unwrap()
val source = "val x = 42\nval y = 43"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
expect tree.source.contains("\n")
```

</details>

#### tracks column positions

- tracks column positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks column positions")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.?
expect tree.source.starts_with("val")
```

</details>

### TreeSitter Tree Versioning

#### initial tree has version 0

- initial tree has version 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initial tree has version 0")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
expect tree.root().?
```

</details>

#### incremental parse increments version

- incremental parse increments version


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("incremental parse increments version")
var parser = TreeSitterParser.new("simple").unwrap()
val tree1 = parser.parse("val x = 42").unwrap()
expect tree1.root().?
```

</details>

### TreeSitter Parse Results

#### returns Ok for valid syntax

- returns Ok for valid syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Ok for valid syntax")
var parser = TreeSitterParser.new("simple").unwrap()
val result = parser.parse("val x = 42")
expect result.ok.?
```

</details>

#### returns tree for valid syntax

- returns tree for valid syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns tree for valid syntax")
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("fn test():\n    42").unwrap()
expect tree.root().?
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0311fbb97aff13a3e2b9073ba96d671ef272f1468ac2d74ead268f62fc672ddf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0311fbb97aff13a3e2b9073ba96d671ef272f1468ac2d74ead268f62fc672ddf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0311fbb97aff13a3e2b9073ba96d671ef272f1468ac2d74ead268f62fc672ddf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/treesitter/treesitter_parser_spec.spl
mirror: doc/06_spec/03_system/feature/features/treesitter/treesitter_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/treesitter/treesitter_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/treesitter/treesitter_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/treesitter/treesitter_parser_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates parser for Simple language' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/treesitter/treesitter_parser_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported languages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/treesitter/treesitter_parser_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates parser with grammar loaded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
