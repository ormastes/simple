# Jit Container I64 Boxing Truncation Repro Specification

> Tests covering JIT container boxing must round-trip every i64 (subprocess differential).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Container I64 Boxing Truncation Repro Specification

## Scenarios

### JIT container boxing must round-trip every i64 (subprocess differential)

#### runs the probe on both engines and gets real output from each

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the probe on both engines and gets real output from each


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the probe on both engines and gets real output from each")
# Non-vacuity gate. If either lane printed nothing, every later
# comparison would trivially 'agree' and the spec would be a lie.
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_true(interp.len() > 0)
assert_true(jit.len() > 0)
assert_true(interp.contains("b60="))
assert_true(jit.contains("b60="))
```

</details>

#### agrees on 2^60 read back out of a list

- agrees on 2^60 read back out of a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on 2^60 read back out of a list")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_line_for(jit, "b60"), _line_for(interp, "b60"))
```

</details>

#### agrees on 2^62 read back out of a list

- agrees on 2^62 read back out of a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on 2^62 read back out of a list")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_line_for(jit, "b62"), _line_for(interp, "b62"))
```

</details>

#### agrees on i64::MAX read back out of a list

- agrees on i64::MAX read back out of a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on i64::MAX read back out of a list")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_line_for(jit, "bmax"), _line_for(interp, "bmax"))
```

</details>

#### agrees on the whole transcript

- agrees on the whole transcript


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on the whole transcript")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(jit, interp)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JIT container boxing must round-trip every i64 (subprocess differential).
- JIT container boxing must round-trip every i64 (subprocess differential)

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

- Canonical SPipe generation for source `adcd2655122c2536faadeb23e3aee30f48e813f19faf5005db985dd5d8c581d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `adcd2655122c2536faadeb23e3aee30f48e813f19faf5005db985dd5d8c581d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `adcd2655122c2536faadeb23e3aee30f48e813f19faf5005db985dd5d8c581d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.spl
mirror: doc/06_spec/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the probe on both engines and gets real output from each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on 2^60 read back out of a list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on 2^62 read back out of a list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
