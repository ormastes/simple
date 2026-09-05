# Trait Static Dispatch Specification

> Tests covering desugar_trait_static_dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Static Dispatch Specification

## Scenarios

### desugar_trait_static_dispatch

#### basic trait param rewrite

#### rewrites single trait param to generic

- rewrites single trait param to generic


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites single trait param to generic")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn process(x: Printable):" + "\n"
src = src + "    x.print_text()" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn process<__T0: Printable>(x: __T0):")
```

</details>

#### rewrites multiple trait params to multiple type vars

- rewrites multiple trait params to multiple type vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites multiple trait params to multiple type vars")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "trait Sortable:" + "\n"
src = src + "    fn sort_key() -> i64" + "\n"
src = src + "\n"
src = src + "fn both(a: Printable, b: Sortable):" + "\n"
src = src + "    0" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn both<__T0: Printable, __T1: Sortable>(a: __T0, b: __T1):")
```

</details>

#### rewrites mixed trait and non-trait params

- rewrites mixed trait and non-trait params


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites mixed trait and non-trait params")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn show(x: Printable, n: i64):" + "\n"
src = src + "    0" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn show<__T0: Printable>(x: __T0, n: i64):")
```

</details>

#### me methods

#### rewrites me method same as fn

- rewrites me method same as fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites me method same as fn")
var src = "trait Updatable:" + "\n"
src = src + "    me update(val: i64)" + "\n"
src = src + "\n"
src = src + "me apply(target: Updatable):" + "\n"
src = src + "    target.update(42)" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("me apply<__T0: Updatable>(target: __T0):")
```

</details>

#### dyn prefix preserves dynamic dispatch

#### does not rewrite dyn Trait params

- does not rewrite dyn Trait params


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite dyn Trait params")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn process(x: dyn Printable):" + "\n"
src = src + "    x.print_text()" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn process(x: dyn Printable):")
```

</details>

#### interface params stay dynamic

#### does not rewrite interface-typed params

- does not rewrite interface-typed params


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite interface-typed params")
var src = "interface Drawable:" + "\n"
src = src + "    fn draw()" + "\n"
src = src + "\n"
src = src + "fn render(x: Drawable):" + "\n"
src = src + "    x.draw()" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn render(x: Drawable):")
```

</details>

#### no-rewrite cases

#### does not rewrite non-trait types

- does not rewrite non-trait types


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite non-trait types")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn add(a: i64, b: i64) -> i64:" + "\n"
src = src + "    a + b" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn add(a: i64, b: i64) -> i64:")
```

</details>

#### does not rewrite already-generic functions

- does not rewrite already-generic functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite already-generic functions")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn process<T: Printable>(x: T):" + "\n"
src = src + "    x.print_text()" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn process<T: Printable>(x: T):")
```

</details>

#### does not rewrite array-typed trait params

- does not rewrite array-typed trait params


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite array-typed trait params")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn process_all(items: [Printable]):" + "\n"
src = src + "    0" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn process_all(items: [Printable]):")
```

</details>

#### source without traits returns unchanged

- source without traits returns unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("source without traits returns unchanged")
var src = "fn add(a: i64, b: i64) -> i64:" + "\n"
src = src + "    a + b" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn add(a: i64, b: i64) -> i64:")
```

</details>

#### return type preservation

#### preserves return type after rewrite

- preserves return type after rewrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves return type after rewrite")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "fn describe(x: Printable) -> text:" + "\n"
src = src + "    x.print_text()" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("fn describe<__T0: Printable>(x: __T0) -> text:")
```

</details>

#### indentation preservation

#### preserves leading indentation

- preserves leading indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves leading indentation")
var src = "trait Printable:" + "\n"
src = src + "    fn print_text() -> text" + "\n"
src = src + "\n"
src = src + "    fn process(x: Printable):" + "\n"
src = src + "        x.print_text()" + "\n"
val out = desugar_trait_static_dispatch(src)
expect(out).to_contain("    fn process<__T0: Printable>(x: __T0):")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/trait_static_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering desugar_trait_static_dispatch.
- desugar_trait_static_dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `a8b85f8b37ab28d4bb2c741e30fe893b88593642102ed67422830aeada628255`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8b85f8b37ab28d4bb2c741e30fe893b88593642102ed67422830aeada628255`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8b85f8b37ab28d4bb2c741e30fe893b88593642102ed67422830aeada628255`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/trait_static_dispatch_spec.spl
mirror: doc/06_spec/unit/app/desugar/trait_static_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/trait_static_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/trait_static_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/trait_static_dispatch_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites single trait param to generic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/trait_static_dispatch_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites multiple trait params to multiple type vars' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/trait_static_dispatch_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites mixed trait and non-trait params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
