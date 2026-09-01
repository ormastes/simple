# Statement Dispatch Class Specification

> Tests covering JS statement keyword dispatch class, locals bound by statements stay resolvable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Statement Dispatch Class Specification

## Scenarios

### JS statement keyword dispatch class

#### switch dispatches as a statement

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- switch dispatches as a statement
   - Expected: eval_str("var r = 'x'; switch (2) { case 2: r = 'two'; break; default: r = 'other'; } r") equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch dispatches as a statement")
expect(eval_str("var r = 'x'; switch (2) { case 2: r = 'two'; break; default: r = 'other'; } r")).to_equal("two")
```

</details>

#### do-while dispatches as a statement

- do-while dispatches as a statement
   - Expected: eval_str("var i = 0; do { i = i + 1; } while (i < 3); String(i)") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("do-while dispatches as a statement")
expect(eval_str("var i = 0; do { i = i + 1; } while (i < 3); String(i)")).to_equal("3")
```

</details>

#### try/catch dispatches as a statement

- try/catch dispatches as a statement
   - Expected: eval_str("var r = 'no'; try { throw 1; } catch (e) { r = 'caught'; } r") equals `caught`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try/catch dispatches as a statement")
expect(eval_str("var r = 'no'; try { throw 1; } catch (e) { r = 'caught'; } r")).to_equal("caught")
```

</details>

#### for-in dispatches as a statement

- for-in dispatches as a statement
   - Expected: eval_str("var n = 0; for (var k in {a:1,b:2}) { n = n + 1; } String(n)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-in dispatches as a statement")
expect(eval_str("var n = 0; for (var k in {a:1,b:2}) { n = n + 1; } String(n)")).to_equal("2")
```

</details>

#### function declaration dispatches as a statement

- function declaration dispatches as a statement
   - Expected: eval_str("function f(a) { return a + 1; } String(f(41))") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function declaration dispatches as a statement")
expect(eval_str("function f(a) { return a + 1; } String(f(41))")).to_equal("42")
```

</details>

#### return inside a function body dispatches as a statement

- return inside a function body dispatches as a statement
   - Expected: eval_str("(function(){ return 'ok'; })()") equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return inside a function body dispatches as a statement")
expect(eval_str("(function(){ return 'ok'; })()")).to_equal("ok")
```

</details>

#### void operator dispatches as an operator

- void operator dispatches as an operator
   - Expected: eval_str("typeof void 0") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("void operator dispatches as an operator")
expect(eval_str("typeof void 0")).to_equal("undefined")
```

</details>

#### delete operator dispatches as an operator

- delete operator dispatches as an operator
   - Expected: eval_str("var o = {a:1}; delete o.a; typeof o.a") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delete operator dispatches as an operator")
expect(eval_str("var o = {a:1}; delete o.a; typeof o.a")).to_equal("undefined")
```

</details>

### locals bound by statements stay resolvable

<details>
<summary>Advanced: a var bound in a for body is readable after the loop</summary>

#### a var bound in a for body is readable after the loop

- a var bound in a for body is readable after the loop
   - Expected: eval_str("for (var i = 0; i < 1; i = i + 1) { var y = 9; } String(y)") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a var bound in a for body is readable after the loop")
expect(eval_str("for (var i = 0; i < 1; i = i + 1) { var y = 9; } String(y)")).to_equal("9")
```

</details>


</details>

<details>
<summary>Advanced: nested loops keep both counters resolvable</summary>

#### nested loops keep both counters resolvable

- nested loops keep both counters resolvable
   - Expected: eval_str("var t = 0; for (var i = 0; i < 3; i = i + 1) { for (var j = 0; j < 2; j = j + 1) { t = t + 1; } } String(t)") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested loops keep both counters resolvable")
expect(eval_str("var t = 0; for (var i = 0; i < 3; i = i + 1) { for (var j = 0; j < 2; j = j + 1) { t = t + 1; } } String(t)")).to_equal("6")
```

</details>


</details>

#### a function-scoped var survives an if statement

- a function-scoped var survives an if statement
   - Expected: eval_str("var x = 1; if (x) { x = x + 1; } String(x)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a function-scoped var survives an if statement")
expect(eval_str("var x = 1; if (x) { x = x + 1; } String(x)")).to_equal("2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/statement_dispatch_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS statement keyword dispatch class, locals bound by statements stay resolvable.
- JS statement keyword dispatch class
- locals bound by statements stay resolvable

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `c77109b70d412da4fb996aaab49c9d725387c6cf4ec52a23e14e68bfc475f46d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c77109b70d412da4fb996aaab49c9d725387c6cf4ec52a23e14e68bfc475f46d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c77109b70d412da4fb996aaab49c9d725387c6cf4ec52a23e14e68bfc475f46d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/js/statement_dispatch_class_spec.spl
mirror: doc/06_spec/01_unit/lib/js/statement_dispatch_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/js/statement_dispatch_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/js/statement_dispatch_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/js/statement_dispatch_class_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'switch dispatches as a statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/statement_dispatch_class_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'do-while dispatches as a statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/statement_dispatch_class_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'try/catch dispatches as a statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
