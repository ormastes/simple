# Static Methods Desugar Specification

> Tests covering desugar_static_methods.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Methods Desugar Specification

## Scenarios

### desugar_static_methods

#### hoists a static fn to module level

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hoists a static fn to module level


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hoists a static fn to module level")
val input = "impl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Point__origin() -> Point:")
expect(output).to_contain("Point(x: 0, y: 0)")
```

</details>

#### removes static keyword from hoisted function

- removes static keyword from hoisted function
   - Expected: has_static is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes static keyword from hoisted function")
val input = "impl Foo:\n    static fn bar() -> i64:\n        42\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Foo__bar() -> i64:")
# Should not contain "static fn" in the hoisted version
val has_static = output.contains("static fn Foo__bar")
expect(has_static).to_equal(false)
```

</details>

#### hoists multiple static methods from same impl

- hoists multiple static methods from same impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hoists multiple static methods from same impl")
val input = "impl Builder:\n    static fn create() -> Builder:\n        Builder(items: [])\n    static fn from_list(items: [text]) -> Builder:\n        Builder(items: items)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Builder__create() -> Builder:")
expect(output).to_contain("fn Builder__from_list(items: [text]) -> Builder:")
```

</details>

#### preserves function parameters in hoisted method

- preserves function parameters in hoisted method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves function parameters in hoisted method")
val input = "impl Parser:\n    static fn new(src: text, mode: i64) -> Parser:\n        Parser(source: src, pos: 0)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Parser__new(src: text, mode: i64) -> Parser:")
```

</details>

#### preserves multi-line body in hoisted method

- preserves multi-line body in hoisted method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves multi-line body in hoisted method")
val input = "impl Config:\n    static fn defaults() -> Config:\n        val x = 10\n        val y = 20\n        Config(x: x, y: y)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Config__defaults() -> Config:")
expect(output).to_contain("val x = 10")
expect(output).to_contain("val y = 20")
```

</details>

#### preserves instance methods in impl block

- preserves instance methods in impl block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves instance methods in impl block")
val input = "impl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)\n    fn distance() -> f64:\n        (self.x ** 2 + self.y ** 2).sqrt()\n"
val output = desugar_static_methods(input)
expect(output).to_contain("impl Point:")
expect(output).to_contain("fn distance() -> f64:")
```

</details>

#### preserves mutable methods (me keyword)

- preserves mutable methods (me keyword)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves mutable methods (me keyword)")
val input = "impl Counter:\n    static fn zero() -> Counter:\n        Counter(count: 0)\n    me increment():\n        self.count = self.count + 1\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Counter__zero() -> Counter:")
expect(output).to_contain("me increment():")
expect(output).to_contain("impl Counter:")
```

</details>

#### keeps multiple instance methods intact

- keeps multiple instance methods intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps multiple instance methods intact")
val input = "impl Widget:\n    fn width() -> i64:\n        self.w\n    fn height() -> i64:\n        self.h\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn width() -> i64:")
expect(output).to_contain("fn height() -> i64:")
```

</details>

#### drops empty impl block when all methods are static

- drops empty impl block when all methods are static
   - Expected: has_impl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops empty impl block when all methods are static")
val input = "impl Config:\n    static fn defaults() -> Config:\n        Config(value: 0)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Config__defaults() -> Config:")
# Should not have an empty impl block
val has_impl = output.contains("impl Config:")
expect(has_impl).to_equal(false)
```

</details>

#### drops impl when multiple static methods removed

- drops impl when multiple static methods removed
   - Expected: has_impl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops impl when multiple static methods removed")
val input = "impl Factory:\n    static fn create() -> Factory:\n        Factory()\n    static fn build(x: i64) -> Factory:\n        Factory(val: x)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Factory__create()")
expect(output).to_contain("fn Factory__build(x: i64)")
val has_impl = output.contains("impl Factory:")
expect(has_impl).to_equal(false)
```

</details>

#### handles trait for type impl pattern

- handles trait for type impl pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles trait for type impl pattern")
val input = "impl Display for Point:\n    fn format() -> text:\n        return self.x\n"
val output = desugar_static_methods(input)
expect(output).to_contain("impl Display for Point:")
expect(output).to_contain("fn format() -> text:")
```

</details>

#### hoists static from trait impl

- hoists static from trait impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hoists static from trait impl")
val input = "impl Parseable for Config:\n    static fn parse(s: text) -> Config:\n        Config(value: s)\n    fn to_string() -> text:\n        self.value\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Config__parse(s: text) -> Config:")
expect(output).to_contain("impl Parseable for Config:")
expect(output).to_contain("fn to_string() -> text:")
```

</details>

#### preserves non-impl code untouched

- preserves non-impl code untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves non-impl code untouched")
val input = "val x = 10\nfn helper() -> i64:\n    42\n"
val output = desugar_static_methods(input)
expect(output).to_contain("val x = 10")
expect(output).to_contain("fn helper() -> i64:")
expect(output).to_contain("42")
```

</details>

#### preserves struct definitions

- preserves struct definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves struct definitions")
val input = "struct Point:\n    x: i64\n    y: i64\n\nimpl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("struct Point:")
expect(output).to_contain("x: i64")
expect(output).to_contain("y: i64")
```

</details>

#### preserves comments

- preserves comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves comments")
val input = "# This is a comment\nimpl Foo:\n    static fn bar() -> i64:\n        1\n"
val output = desugar_static_methods(input)
expect(output).to_contain("# This is a comment")
```

</details>

#### preserves blank lines between non-impl code

- preserves blank lines between non-impl code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves blank lines between non-impl code")
val input = "val a = 1\n\nval b = 2\n"
val output = desugar_static_methods(input)
expect(output).to_contain("val a = 1")
expect(output).to_contain("val b = 2")
```

</details>

#### handles multiple separate impl blocks

- handles multiple separate impl blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple separate impl blocks")
val input = "impl Foo:\n    static fn create() -> Foo:\n        Foo()\n\nimpl Bar:\n    static fn build() -> Bar:\n        Bar()\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Foo__create() -> Foo:")
expect(output).to_contain("fn Bar__build() -> Bar:")
```

</details>

#### handles impl block with mixed methods followed by another impl

- handles impl block with mixed methods followed by another impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles impl block with mixed methods followed by another impl")
val input = "impl A:\n    static fn make() -> A:\n        A()\n    fn get() -> i64:\n        self.val\n\nimpl B:\n    fn show() -> text:\n        self.name\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn A__make() -> A:")
expect(output).to_contain("impl A:")
expect(output).to_contain("fn get() -> i64:")
expect(output).to_contain("impl B:")
expect(output).to_contain("fn show() -> text:")
```

</details>

#### handles impl with generic type

- handles impl with generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles impl with generic type")
val input = "impl Container<T>:\n    static fn empty() -> Container:\n        Container(items: [])\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Container__empty")
```

</details>

#### strips generics from type name in hoisted function

- strips generics from type name in hoisted function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips generics from type name in hoisted function")
val input = "impl Option<T>:\n    static fn none() -> Option:\n        nil\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Option__none")
```

</details>

#### de-indents hoisted method body to module level

- de-indents hoisted method body to module level


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("de-indents hoisted method body to module level")
val input = "impl Math:\n    static fn add(a: i64, b: i64) -> i64:\n        a + b\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Math__add(a: i64, b: i64) -> i64:")
expect(output).to_contain("a + b")
```

</details>

#### handles deeply nested body in hoisted method

- handles deeply nested body in hoisted method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles deeply nested body in hoisted method")
val input = "impl Logic:\n    static fn check(x: i64) -> bool:\n        if x > 0:\n            return true\n        false\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Logic__check(x: i64) -> bool:")
expect(output).to_contain("if x > 0:")
expect(output).to_contain("return true")
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
val output = desugar_static_methods("")
expect(output).to_equal("")
```

</details>

#### handles input with no impl blocks

- handles input with no impl blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles input with no impl blocks")
val input = "fn standalone():\n    pass\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn standalone():")
```

</details>

#### handles impl with only instance methods unchanged

- handles impl with only instance methods unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles impl with only instance methods unchanged")
val input = "impl Simple:\n    fn value() -> i64:\n        0\n"
val output = desugar_static_methods(input)
expect(output).to_contain("impl Simple:")
expect(output).to_contain("fn value() -> i64:")
```

</details>

#### handles static fn with no return type

- handles static fn with no return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles static fn with no return type")
val input = "impl Logger:\n    static fn init():\n        print \"init\"\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Logger__init():")
```

</details>

#### preserves return type annotation

- preserves return type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves return type annotation")
val input = "impl Creator:\n    static fn make(n: i64) -> Creator:\n        Creator(n: n)\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Creator__make(n: i64) -> Creator:")
```

</details>

#### handles static method with complex body

- handles static method with complex body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles static method with complex body")
val input = "impl Validator:\n    static fn is_valid(s: text) -> bool:\n        val len = s.len()\n        if len == 0:\n            return false\n        if len > 100:\n            return false\n        true\n"
val output = desugar_static_methods(input)
expect(output).to_contain("fn Validator__is_valid(s: text) -> bool:")
expect(output).to_contain("val len = s.len()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/static_methods_desugar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering desugar_static_methods.
- desugar_static_methods

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
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

- Canonical SPipe generation for source `390e13be3193934bf6518c1f98624cb8d7b9b0b076e44dea55fe9e330053b191`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `390e13be3193934bf6518c1f98624cb8d7b9b0b076e44dea55fe9e330053b191`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `390e13be3193934bf6518c1f98624cb8d7b9b0b076e44dea55fe9e330053b191`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/static_methods_desugar_spec.spl
mirror: doc/06_spec/unit/app/desugar/static_methods_desugar_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/static_methods_desugar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/static_methods_desugar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/static_methods_desugar_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hoists a static fn to module level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/static_methods_desugar_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes static keyword from hoisted function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/static_methods_desugar_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hoists multiple static methods from same impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
