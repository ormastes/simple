# Rewriter Static Calls Specification

> Tests covering rewrite_static_calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rewriter Static Calls Specification

## Scenarios

### rewrite_static_calls

#### rewrites Type.method() to Type__method()

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rewrites Type.method() to Type__method()


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites Type.method() to Type__method()")
val input = "val p = Point.origin()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Point__origin()")
```

</details>

#### rewrites call with arguments

- rewrites call with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call with arguments")
val input = "val p = Point.from_pair(1, 2)\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Point__from_pair(1, 2)")
```

</details>

#### rewrites call with no arguments

- rewrites call with no arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call with no arguments")
val input = "Config.defaults()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Config__defaults()")
```

</details>

#### rewrites call with text argument

- rewrites call with text argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call with text argument")
val input = "val parser = Parser.from_source(src)\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Parser__from_source(src)")
```

</details>

#### replaces dot with double underscore

- replaces dot with double underscore
   - Expected: has_dot is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces dot with double underscore")
val input = "Builder.create()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Builder__create()")
val has_dot = output.contains("Builder.create()")
expect(has_dot).to_equal(false)
```

</details>

#### does not rewrite instance method calls (lowercase receiver)

- does not rewrite instance method calls (lowercase receiver)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite instance method calls (lowercase receiver)")
val input = "val d = point.distance()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("point.distance()")
```

</details>

#### does not rewrite self access

- does not rewrite self access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite self access")
val input = "self.field\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("self.field")
```

</details>

#### does not rewrite lowercase variable method calls

- does not rewrite lowercase variable method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite lowercase variable method calls")
val input = "result.unwrap()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("result.unwrap()")
```

</details>

#### does not rewrite field access without parens

- does not rewrite field access without parens


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite field access without parens")
val input = "val x = point.x\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("point.x")
```

</details>

#### rewrites Uppercase.field even without parens

- rewrites Uppercase.field even without parens


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites Uppercase.field even without parens")
val input = "val n = Config.name\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Config__name")
```

</details>

#### skips comment lines entirely

- skips comment lines entirely


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips comment lines entirely")
val input = "# Point.origin() is a factory\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("# Point.origin() is a factory")
```

</details>

#### does not rewrite inside string literals

- does not rewrite inside string literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite inside string literals")
val input = "val s = \"Point.origin()\"\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("\"Point.origin()\"")
```

</details>

#### skips import/use lines

- skips import/use lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips import/use lines")
val input = "use app.desugar.rewriter (rewrite_static_calls)\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("use app.desugar.rewriter (rewrite_static_calls)")
```

</details>

#### skips export lines

- skips export lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips export lines")
val input = "export Point, Config\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("export Point, Config")
```

</details>

#### skips impl definition lines

- skips impl definition lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips impl definition lines")
val input = "impl Point:\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("impl Point:")
```

</details>

#### skips class definition lines

- skips class definition lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips class definition lines")
val input = "class Widget:\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("class Widget:")
```

</details>

#### skips struct definition lines

- skips struct definition lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips struct definition lines")
val input = "struct Data:\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("struct Data:")
```

</details>

#### skips enum definition lines

- skips enum definition lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips enum definition lines")
val input = "enum Color:\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("enum Color:")
```

</details>

#### skips static fn definition lines

- skips static fn definition lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips static fn definition lines")
val input = "static fn Point__origin() -> Point:\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("static fn Point__origin()")
```

</details>

#### rewrites nested static calls

- rewrites nested static calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites nested static calls")
val input = "val r = Type.method(Other.factory())\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Type__method(Other__factory())")
```

</details>

#### rewrites multiple static calls on same line

- rewrites multiple static calls on same line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites multiple static calls on same line")
val input = "val x = Foo.bar() + Baz.qux()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Foo__bar()")
expect(output).to_contain("Baz__qux()")
```

</details>

#### rewrites call in assignment

- rewrites call in assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call in assignment")
val input = "var config = Config.load(path)\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Config__load(path)")
```

</details>

#### rewrites call in if condition

- rewrites call in if condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call in if condition")
val input = "if Validator.check(x):\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Validator__check(x)")
```

</details>

#### rewrites call in return statement

- rewrites call in return statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call in return statement")
val input = "return Factory.create()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Factory__create()")
```

</details>

#### rewrites call in val binding

- rewrites call in val binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites call in val binding")
val input = "val result = Builder.from_args(a, b, c)\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Builder__from_args(a, b, c)")
```

</details>

#### rewrites across multiple lines

- rewrites across multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites across multiple lines")
val input = "val a = Foo.bar()\nval b = Baz.qux()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Foo__bar()")
expect(output).to_contain("Baz__qux()")
```

</details>

#### preserves non-static lines among static calls

- preserves non-static lines among static calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves non-static lines among static calls")
val input = "val x = 10\nval p = Point.origin()\nval y = 20\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("val x = 10")
expect(output).to_contain("Point__origin()")
expect(output).to_contain("val y = 20")
```

</details>

#### handles mix of comments and code

- handles mix of comments and code


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mix of comments and code")
val input = "# factory call\nval p = Point.origin()\n# done\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("# factory call")
expect(output).to_contain("Point__origin()")
expect(output).to_contain("# done")
```

</details>

#### does not rewrite when uppercase word is part of longer word

- does not rewrite when uppercase word is part of longer word


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite when uppercase word is part of longer word")
val input = "val myPoint = getPoint.origin()\n"
val output = rewrite_static_calls(input)
# "getPoint" starts with lowercase g, so it's an instance call
expect(output).to_contain("getPoint.origin()")
```

</details>

#### rewrites when preceded by space

- rewrites when preceded by space


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites when preceded by space")
val input = "val x = Point.new()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Point__new()")
```

</details>

#### rewrites when preceded by opening paren

- rewrites when preceded by opening paren


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites when preceded by opening paren")
val input = "call(Point.new())\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Point__new()")
```

</details>

#### rewrites when preceded by equals sign

- rewrites when preceded by equals sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites when preceded by equals sign")
val input = "x=Point.new()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Point__new()")
```

</details>

#### handles empty input

- handles empty input
   - Expected: output equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty input")
val output = rewrite_static_calls("")
expect(output).to_equal("")
```

</details>

#### handles single newline

- handles single newline
   - Expected: output equals `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single newline")
val output = rewrite_static_calls("\n")
expect(output).to_equal("\n")
```

</details>

#### handles short lines (less than 3 chars)

- handles short lines (less than 3 chars)
   - Expected: output equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles short lines (less than 3 chars)")
val output = rewrite_static_calls("ab")
expect(output).to_equal("ab")
```

</details>

#### handles line with only spaces

- handles line with only spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles line with only spaces")
val output = rewrite_static_calls("    \n")
expect(output).to_contain("    ")
```

</details>

#### handles type name with underscores

- handles type name with underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles type name with underscores")
val input = "val x = My_Type.create()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("My_Type__create()")
```

</details>

#### handles method name with underscores

- handles method name with underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles method name with underscores")
val input = "val x = Point.from_polar(r, theta)\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Point__from_polar(r, theta)")
```

</details>

#### does not rewrite method call on number

- does not rewrite method call on number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite method call on number")
val input = "val x = 42.to_string()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("42.to_string()")
```

</details>

#### handles chained: Type.static().instance_method()

- handles chained: Type.static().instance_method()


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles chained: Type.static().instance_method()")
val input = "val r = Builder.create().build()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("Builder__create().build()")
```

</details>

#### preserves indented code

- preserves indented code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves indented code")
val input = "    val p = Point.origin()\n"
val output = rewrite_static_calls(input)
expect(output).to_contain("    ")
expect(output).to_contain("Point__origin()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/rewriter_static_calls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rewrite_static_calls.
- rewrite_static_calls

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

- Canonical SPipe generation for source `9758f749f1cca046457da4b12e149edb8f89350522631b7ea453d58b9e117816`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9758f749f1cca046457da4b12e149edb8f89350522631b7ea453d58b9e117816`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9758f749f1cca046457da4b12e149edb8f89350522631b7ea453d58b9e117816`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/rewriter_static_calls_spec.spl
mirror: doc/06_spec/unit/app/desugar/rewriter_static_calls_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/rewriter_static_calls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/rewriter_static_calls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/rewriter_static_calls_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites Type.method() to Type__method()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/rewriter_static_calls_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites call with arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/rewriter_static_calls_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites call with no arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
