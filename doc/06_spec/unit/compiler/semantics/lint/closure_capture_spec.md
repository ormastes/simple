# Closure Capture Specification

> Tests covering Closure Capture Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Closure Capture Specification

## Scenarios

### Closure Capture Lint

#### closure modifying outer variable

#### flags nested fn that modifies an outer var (CLOS001)

- flags nested fn that modifies an outer var (CLOS001)
   - Expected: has_clos001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags nested fn that modifies an outer var (CLOS001)")
val code = "fn compute():\n    var counter = 0\n    fn inc():\n        counter = counter + 1\n    inc()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(true)
```

</details>

#### flags nested fn that reassigns outer var

- flags nested fn that reassigns outer var
   - Expected: has_clos001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags nested fn that reassigns outer var")
val code = "fn test():\n    var x = 10\n    fn update():\n        x = 42\n    update()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(true)
```

</details>

#### closure reading outer variable

#### does not flag nested fn that only reads outer var

- does not flag nested fn that only reads outer var
   - Expected: has_clos001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag nested fn that only reads outer var")
val code = "fn compute() -> i64:\n    val x = 10\n    fn double() -> i64:\n        x * 2\n    double()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

#### does not flag nested fn reading outer val

- does not flag nested fn reading outer val
   - Expected: has_clos001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag nested fn reading outer val")
val code = "fn greet():\n    val name = \"Alice\"\n    fn say():\n        print \"Hello\"\n    say()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

#### module-level var mutation

#### does not flag module-level var mutation

- does not flag module-level var mutation
   - Expected: has_clos001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag module-level var mutation")
val code = "var global_count = 0\n\nfn increment():\n    global_count = global_count + 1\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

#### does not flag module-level var push

- does not flag module-level var push
   - Expected: has_clos001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag module-level var push")
val code = "var items: [text] = []\n\nfn add_item(item: text):\n    items.push(item)\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/lint/closure_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Closure Capture Lint.
- Closure Capture Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `ec1910b954066134e2281d7b53f106e850c5ec745734c4c0550a7c9bce8af20e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec1910b954066134e2281d7b53f106e850c5ec745734c4c0550a7c9bce8af20e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec1910b954066134e2281d7b53f106e850c5ec745734c4c0550a7c9bce8af20e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/unit/compiler/semantics/lint/closure_capture_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/lint/closure_capture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/lint/closure_capture_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/unit/compiler/semantics/lint/closure_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/lint/closure_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
