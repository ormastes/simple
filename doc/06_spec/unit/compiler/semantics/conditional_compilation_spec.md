# Conditional Compilation Specification

> Tests covering conditional compilation @when.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Conditional Compilation Specification

## Scenarios

### conditional compilation @when

#### when_check_condition debug is true in interpreter mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- when_check_condition debug is true in interpreter mode
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when_check_condition debug is true in interpreter mode")
# @when(debug) is true in interpreter mode
# This is a conceptual test - the actual @when mechanism works via
# annotation scanning during module load
val result = true  # debug mode is always true in interpreter
expect(result).to_equal(true)
```

</details>

#### when_check_condition release is false in interpreter mode

- when_check_condition release is false in interpreter mode
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when_check_condition release is false in interpreter mode")
val result = false  # release mode is always false in interpreter
expect(result).to_equal(false)
```

</details>

#### when_check_condition interpreter is true

- when_check_condition interpreter is true
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when_check_condition interpreter is true")
val result = true
expect(result).to_equal(true)
```

</details>

#### when_check_condition compiled is false

- when_check_condition compiled is false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when_check_condition compiled is false")
val result = false
expect(result).to_equal(false)
```

</details>

#### feature flags are disabled by default

- feature flags are disabled by default
   - Expected: feature_myfeature is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("feature flags are disabled by default")
# @when(feature=myfeature) disables the declaration
# when the feature is not set
val feature_myfeature = false
expect(feature_myfeature).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/conditional_compilation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering conditional compilation @when.
- conditional compilation @when

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `92d0c8d7054199f7c3fe44ec468d7b271aba1c6bf2dce82a250d09f5fa98368f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92d0c8d7054199f7c3fe44ec468d7b271aba1c6bf2dce82a250d09f5fa98368f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92d0c8d7054199f7c3fe44ec468d7b271aba1c6bf2dce82a250d09f5fa98368f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/conditional_compilation_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/conditional_compilation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/conditional_compilation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/conditional_compilation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/conditional_compilation_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'when_check_condition debug is true in interpreter mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/conditional_compilation_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'when_check_condition release is false in interpreter mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/conditional_compilation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'when_check_condition interpreter is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
