# Rewriter Constants Specification

> Tests covering static constant call rewriting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rewriter Constants Specification

## Scenarios

### static constant call rewriting

#### rewrites simple constant access

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rewrites simple constant access
   - Expected: output equals `val x = Point__ORIGIN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites simple constant access")
val input = "val x = Point.ORIGIN"
val output = rewrite_static_calls(input)

expect(output).to_equal("val x = Point__ORIGIN")
```

</details>

#### rewrites multiple constant accesses on same line

- rewrites multiple constant accesses on same line
   - Expected: output equals `val bounds = Rect(Point__MIN, Point__MAX)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites multiple constant accesses on same line")
val input = "val bounds = Rect(Point.MIN, Point.MAX)"
val output = rewrite_static_calls(input)

expect(output).to_equal("val bounds = Rect(Point__MIN, Point__MAX)")
```

</details>

#### rewrites constants in expressions

- rewrites constants in expressions
   - Expected: output equals `if x > Config__MAX_SIZE:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in expressions")
val input = "if x > Config.MAX_SIZE:"
val output = rewrite_static_calls(input)

expect(output).to_equal("if x > Config__MAX_SIZE:")
```

</details>

#### rewrites constants in function arguments

- rewrites constants in function arguments
   - Expected: output equals `fn process(limit: i64 = Settings__DEFAULT_LIMIT):`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in function arguments")
val input = "fn process(limit: i64 = Settings.DEFAULT_LIMIT):"
val output = rewrite_static_calls(input)

expect(output).to_equal("fn process(limit: i64 = Settings__DEFAULT_LIMIT):")
```

</details>

#### distinguishes between method calls and constant access

- distinguishes between method calls and constant access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes between method calls and constant access")
val input = "val p = Point.origin()\nval c = Color.RED"
val output = rewrite_static_calls(input)

expect(output).to_contain("Point__origin()")
expect(output).to_contain("Color__RED")
```

</details>

#### rewrites constants with lowercase method names

- rewrites constants with lowercase method names
   - Expected: output equals `val x = Config__default_timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants with lowercase method names")
val input = "val x = Config.default_timeout"
val output = rewrite_static_calls(input)

expect(output).to_equal("val x = Config__default_timeout")
```

</details>

#### does not rewrite instance field access

- does not rewrite instance field access
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite instance field access")
val input = "val x = obj.field_name"
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### does not rewrite self access

- does not rewrite self access
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite self access")
val input = "val x = self.value"
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### preserves string literals with dots

- preserves string literals with dots
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves string literals with dots")
val input = "val s = \"Type.CONSTANT\""
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### rewrites constants in array literals

- rewrites constants in array literals
   - Expected: output equals `val colors = [Color__RED, Color__GREEN, Color__BLUE]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in array literals")
val input = "val colors = [Color.RED, Color.GREEN, Color.BLUE]"
val output = rewrite_static_calls(input)

expect(output).to_equal("val colors = [Color__RED, Color__GREEN, Color__BLUE]")
```

</details>

#### rewrites constants in return statements

- rewrites constants in return statements
   - Expected: output equals `return Error__NOT_FOUND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in return statements")
val input = "return Error.NOT_FOUND"
val output = rewrite_static_calls(input)

expect(output).to_equal("return Error__NOT_FOUND")
```

</details>

#### rewrites constants in comparisons

- rewrites constants in comparisons
   - Expected: output equals `if status == Status__SUCCESS:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in comparisons")
val input = "if status == Status.SUCCESS:"
val output = rewrite_static_calls(input)

expect(output).to_equal("if status == Status__SUCCESS:")
```

</details>

#### rewrites constants in arithmetic

- rewrites constants in arithmetic
   - Expected: output equals `val area = Math__PI * r * r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in arithmetic")
val input = "val area = Math.PI * r * r"
val output = rewrite_static_calls(input)

expect(output).to_equal("val area = Math__PI * r * r")
```

</details>

#### handles nested constant access

- handles nested constant access
   - Expected: output equals `val x = Outer__Inner__CONSTANT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested constant access")
val input = "val x = Outer.Inner.CONSTANT"
val output = rewrite_static_calls(input)

expect(output).to_equal("val x = Outer__Inner__CONSTANT")
```

</details>

#### rewrites constants with underscores

- rewrites constants with underscores
   - Expected: output equals `val size = Config__MAX_BUFFER_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants with underscores")
val input = "val size = Config.MAX_BUFFER_SIZE"
val output = rewrite_static_calls(input)

expect(output).to_equal("val size = Config__MAX_BUFFER_SIZE")
```

</details>

#### handles mixed static members on same line

- handles mixed static members on same line
   - Expected: output equals `val p = Point__origin(Point__ZERO, Math__PI)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mixed static members on same line")
val input = "val p = Point.origin(Point.ZERO, Math.PI)"
val output = rewrite_static_calls(input)

expect(output).to_equal("val p = Point__origin(Point__ZERO, Math__PI)")
```

</details>

#### preserves comments

- preserves comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves comments")
val input = "# Use the default value\nval x = Config.DEFAULT"
val output = rewrite_static_calls(input)

expect(output).to_contain("# Use the default value")
expect(output).to_contain("Config__DEFAULT")
```

</details>

#### does not rewrite use statements

- does not rewrite use statements
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite use statements")
val input = "use Config.MAX_SIZE"
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### does not rewrite import statements

- does not rewrite import statements
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite import statements")
val input = "import Point.ORIGIN"
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### does not rewrite export statements

- does not rewrite export statements
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite export statements")
val input = "export Point.ORIGIN"
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### handles constants in struct initialization

- handles constants in struct initialization
   - Expected: output equals `val cfg = Config(max: Limits__MAX, min: Limits__MIN)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in struct initialization")
val input = "val cfg = Config(max: Limits.MAX, min: Limits.MIN)"
val output = rewrite_static_calls(input)

expect(output).to_equal("val cfg = Config(max: Limits__MAX, min: Limits__MIN)")
```

</details>

#### handles constants in match patterns

- handles constants in match patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in match patterns")
val input = "match status:\n    Status.SUCCESS: handle_success()"
val output = rewrite_static_calls(input)

expect(output).to_contain("Status__SUCCESS")
```

</details>

#### handles constants with numeric suffixes

- handles constants with numeric suffixes
   - Expected: output equals `val err = Error__E404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with numeric suffixes")
val input = "val err = Error.E404"
val output = rewrite_static_calls(input)

expect(output).to_equal("val err = Error__E404")
```

</details>

#### rewrites constants in binary operations

- rewrites constants in binary operations
   - Expected: output equals `val result = x + Config__OFFSET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites constants in binary operations")
val input = "val result = x + Config.OFFSET"
val output = rewrite_static_calls(input)

expect(output).to_equal("val result = x + Config__OFFSET")
```

</details>

#### handles constants in logical operations

- handles constants in logical operations
   - Expected: output equals `if enabled and Config__DEBUG_MODE:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in logical operations")
val input = "if enabled and Config.DEBUG_MODE:"
val output = rewrite_static_calls(input)

expect(output).to_equal("if enabled and Config__DEBUG_MODE:")
```

</details>

#### handles constants in ternary-like expressions

- handles constants in ternary-like expressions
   - Expected: output equals `val v = if cond: Defaults__A else: Defaults__B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in ternary-like expressions")
val input = "val v = if cond: Defaults.A else: Defaults.B"
val output = rewrite_static_calls(input)

expect(output).to_equal("val v = if cond: Defaults__A else: Defaults__B")
```

</details>

#### handles constants in list comprehensions

- handles constants in list comprehensions
   - Expected: output equals `val items = [for x in range(Limits__MAX): x * 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in list comprehensions")
val input = "val items = [for x in range(Limits.MAX): x * 2]"
val output = rewrite_static_calls(input)

expect(output).to_equal("val items = [for x in range(Limits__MAX): x * 2]")
```

</details>

#### handles constants in print statements

- handles constants in print statements
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in print statements")
# The braces are doubled so this spec's own literal is not interpolated;
# `input` still holds the single-brace text `print "Value: {Config.DEFAULT_VALUE}"`.
val input = "print \"Value: {{Config.DEFAULT_VALUE}}\""
val output = rewrite_static_calls(input)

# String interpolation should be preserved, but we don't expand inside strings
expect(output).to_equal(input)
```

</details>

#### handles multiple lines with constants

- handles multiple lines with constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple lines with constants")
val input = "val a = Point.ZERO\nval b = Point.UNIT_X\nval c = Point.UNIT_Y"
val output = rewrite_static_calls(input)

expect(output).to_contain("Point__ZERO")
expect(output).to_contain("Point__UNIT_X")
expect(output).to_contain("Point__UNIT_Y")
```

</details>

#### handles constants after method calls

- handles constants after method calls
   - Expected: output equals `val x = obj.method() + Config__OFFSET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants after method calls")
val input = "val x = obj.method() + Config.OFFSET"
val output = rewrite_static_calls(input)

expect(output).to_equal("val x = obj.method() + Config__OFFSET")
```

</details>

#### does not rewrite lowercase receiver

- does not rewrite lowercase receiver
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite lowercase receiver")
val input = "val x = config.MAX_SIZE"
val output = rewrite_static_calls(input)

expect(output).to_equal(input)
```

</details>

#### handles constants in function return types

- handles constants in function return types
   - Expected: output equals `fn get_max() -> Config__MAX_TYPE:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in function return types")
# This is a declaration, not a call, so should be preserved
val input = "fn get_max() -> Config.MAX_TYPE:"
val output = rewrite_static_calls(input)

# Type annotations might contain Type.Member, but those should be rewritten too
expect(output).to_equal("fn get_max() -> Config__MAX_TYPE:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/rewriter_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering static constant call rewriting.
- static constant call rewriting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `721d1fa3475bf837c18460348b862dddf4911a0494c221a515a651bfefe3ee6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `721d1fa3475bf837c18460348b862dddf4911a0494c221a515a651bfefe3ee6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `721d1fa3475bf837c18460348b862dddf4911a0494c221a515a651bfefe3ee6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/rewriter_constants_spec.spl
mirror: doc/06_spec/unit/app/desugar/rewriter_constants_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/rewriter_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/rewriter_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/rewriter_constants_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites simple constant access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/rewriter_constants_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites multiple constant accesses on same line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/rewriter_constants_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites constants in expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
