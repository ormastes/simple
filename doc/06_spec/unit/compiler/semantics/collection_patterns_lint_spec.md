# Collection Patterns Lint Specification

> Tests covering COLL001 - Array concat in loop, COLL002 - .contains() on array in loop, COLL003 - .remove(0) queue drain, COLL004 - Loop-invariant method call, COLL005 - Chained .filter().filter().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Patterns Lint Specification

## Scenarios

### COLL001 - Array concat in loop

<details>
<summary>Advanced: warns on arr = arr + [x] in while loop</summary>

#### warns on arr = arr + [x] in while loop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warns on arr = arr + [x] in while loop
   - Expected: has_code(warnings, "COLL001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on arr = arr + [x] in while loop")
val code = "fn process():\n    var items = []\n    var i = 0\n    while i < 10:\n        items = items + [i]\n        i = i + 1\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL001")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: warns on arr = arr + [x] in for loop</summary>

#### warns on arr = arr + [x] in for loop

- warns on arr = arr + [x] in for loop
   - Expected: has_code(warnings, "COLL001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on arr = arr + [x] in for loop")
val code = "fn build():\n    var result = []\n    for x in 0..10:\n        result = result + [x]\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL001")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not warn outside loop</summary>

#### does not warn outside loop

- does not warn outside loop
   - Expected: has_code(warnings, "COLL001") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn outside loop")
val code = "fn once():\n    var items = []\n    items = items + [1]\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL001")).to_equal(false)
```

</details>


</details>

### COLL002 - .contains() on array in loop

<details>
<summary>Advanced: warns on .contains() inside while loop</summary>

#### warns on .contains() inside while loop

- warns on .contains() inside while loop
   - Expected: has_code(warnings, "COLL002") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on .contains() inside while loop")
val code = "fn search(data: [i64]):\n    var i = 0\n    while i < 100:\n        data.contains(i)\n        i = i + 1\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL002")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not warn on .contains() outside loop</summary>

#### does not warn on .contains() outside loop

- does not warn on .contains() outside loop
   - Expected: has_code(warnings, "COLL002") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn on .contains() outside loop")
val code = "fn check(data: [i64]):\n    data.contains(5)\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL002")).to_equal(false)
```

</details>


</details>

### COLL003 - .remove(0) queue drain

<details>
<summary>Advanced: warns on .remove(0) in while loop</summary>

#### warns on .remove(0) in while loop

- warns on .remove(0) in while loop
   - Expected: has_code(warnings, "COLL003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on .remove(0) in while loop")
val code = "fn drain(queue: [i64]):\n    while queue.len() > 0:\n        queue.remove(0)\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL003")).to_equal(true)
```

</details>


</details>

#### does not warn on .remove(1)

- does not warn on .remove(1)
   - Expected: has_code(warnings, "COLL003") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn on .remove(1)")
val code = "fn drain(queue: [i64]):\n    while queue.len() > 0:\n        queue.remove(1)\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL003")).to_equal(false)
```

</details>

### COLL004 - Loop-invariant method call

<details>
<summary>Advanced: warns on external .len() call in for loop</summary>

#### warns on external .len() call in for loop

- warns on external .len() call in for loop
   - Expected: has_code(warnings, "COLL004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on external .len() call in for loop")
val code = "fn process(data: [i64]):\n    for x in 0..100:\n        data.len()\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL004")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not warn when receiver is loop variable</summary>

#### does not warn when receiver is loop variable

- does not warn when receiver is loop variable
   - Expected: has_code(warnings, "COLL004") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn when receiver is loop variable")
val code = "fn process(items: [[i64]]):\n    for item in items:\n        item.len()\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL004")).to_equal(false)
```

</details>


</details>

### COLL005 - Chained .filter().filter()

#### warns on .filter().filter() chain

- warns on .filter().filter() chain
   - Expected: has_code(warnings, "COLL005") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on .filter().filter() chain")
val code = "fn process(data: [i64]):\n    val result = data.filter(\\x: x > 0).filter(\\x: x < 100)\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL005")).to_equal(true)
```

</details>

#### does not warn on single .filter()

- does not warn on single .filter()
   - Expected: has_code(warnings, "COLL005") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn on single .filter()")
val code = "fn process(data: [i64]):\n    val result = data.filter(\\x: x > 0)\n"
val warnings = analyze(code)
expect(has_code(warnings, "COLL005")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/collection_patterns_lint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering COLL001 - Array concat in loop, COLL002 - .contains() on array in loop, COLL003 - .remove(0) queue drain, COLL004 - Loop-invariant method call, COLL005 - Chained .filter().filter().
- COLL001 - Array concat in loop
- COLL002 - .contains() on array in loop
- COLL003 - .remove(0) queue drain
- COLL004 - Loop-invariant method call
- COLL005 - Chained .filter().filter()

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

- Canonical SPipe generation for source `13bc9bbb3ca3d75b22e1418b229d810c7d12c8b0e1303b76915fb1b09995af38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13bc9bbb3ca3d75b22e1418b229d810c7d12c8b0e1303b76915fb1b09995af38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13bc9bbb3ca3d75b22e1418b229d810c7d12c8b0e1303b76915fb1b09995af38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/collection_patterns_lint_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/collection_patterns_lint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/collection_patterns_lint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/collection_patterns_lint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/collection_patterns_lint_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on arr = arr + [x] in while loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/collection_patterns_lint_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on arr = arr + [x] in for loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/collection_patterns_lint_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not warn outside loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
