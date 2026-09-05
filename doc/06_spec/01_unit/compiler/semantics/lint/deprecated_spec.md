# Deprecated Specification

> Tests covering Deprecated Usage Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deprecated Specification

## Scenarios

### Deprecated Usage Lint

#### DEPR001 - Type__method() syntax

#### flags Type__method() call pattern as DEPR001

- flags Type__method() call pattern as DEPR001
   - Expected: has_depr001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags Type__method() call pattern as DEPR001")
val code = "fn test():\n    val result = Vec__new()\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(true)
```

</details>

#### flags String__from() as DEPR001

- flags String__from() as DEPR001
   - Expected: has_depr001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags String__from() as DEPR001")
val code = "fn test():\n    val s = String__from(\"hello\")\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(true)
```

</details>

#### does not flag dunder names like __init__

- does not flag dunder names like __init__
   - Expected: has_depr001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag dunder names like __init__")
val code = "fn __init__():\n    print \"init\"\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(false)
```

</details>

#### does not flag normal function calls

- does not flag normal function calls
   - Expected: has_depr001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag normal function calls")
val code = "fn test():\n    val x = compute_value()\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(false)
```

</details>

#### DEPR002 - .new() constructor

#### flags .new() constructor as DEPR002

- flags .new() constructor as DEPR002
   - Expected: has_depr002 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags .new() constructor as DEPR002")
val code = "fn test():\n    val p = Point.new(1, 2)\n"
val codes = check_deprecated_text(code)
val has_depr002 = codes_contain(codes, "DEPR002")
expect(has_depr002).to_equal(true)
```

</details>

#### does not flag methods named new_item

- does not flag methods named new_item
   - Expected: has_depr002 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag methods named new_item")
val code = "fn test():\n    val x = create_new_item()\n"
val codes = check_deprecated_text(code)
val has_depr002 = codes_contain(codes, "DEPR002")
expect(has_depr002).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/deprecated_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Deprecated Usage Lint.
- Deprecated Usage Lint

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

- Canonical SPipe generation for source `2a6d803ed95489609637bd61a82ef74391e1de1f87b4c2fd7814e0630b62d1f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a6d803ed95489609637bd61a82ef74391e1de1f87b4c2fd7814e0630b62d1f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a6d803ed95489609637bd61a82ef74391e1de1f87b4c2fd7814e0630b62d1f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/deprecated_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/deprecated_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/deprecated_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/deprecated_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/deprecated_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags Type__method() call pattern as DEPR001' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/deprecated_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags String__from() as DEPR001' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/deprecated_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag dunder names like __init__' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
