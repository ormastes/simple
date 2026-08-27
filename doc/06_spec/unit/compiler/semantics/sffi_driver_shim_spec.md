# Sffi Driver Shim Specification

> Tests covering SFFI007 driver shim conformance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sffi Driver Shim Specification

## Scenarios

### SFFI007 driver shim conformance

#### errors when a @driver module has extern functions but no Driver impl

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- errors when a @driver module has extern functions but no Driver impl
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI007`
   - Expected: warnings[0].severity equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors when a @driver module has extern functions but no Driver impl")
val warnings = check_sffi007_driver_shim(true, true, false, "nvme", "nvme.spl")

expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI007")
expect(warnings[0].severity).to_equal("ERROR")
expect(warnings[0].message).to_contain("no `impl Driver for X`")
```

</details>

#### passes when the @driver extern shim has a Driver impl

- passes when the @driver extern shim has a Driver impl
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes when the @driver extern shim has a Driver impl")
val warnings = check_sffi007_driver_shim(true, true, true, "nvme", "nvme.spl")

expect(warnings.len()).to_equal(0)
```

</details>

#### ignores modules without extern driver shims

- ignores modules without extern driver shims
   - Expected: check_sffi007_driver_shim(false, true, false, "pure", "pure.spl").len() equals `0`
   - Expected: check_sffi007_driver_shim(true, false, false, "native", "native.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores modules without extern driver shims")
expect(check_sffi007_driver_shim(false, true, false, "pure", "pure.spl").len()).to_equal(0)
expect(check_sffi007_driver_shim(true, false, false, "native", "native.spl").len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/sffi_driver_shim_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SFFI007 driver shim conformance.
- SFFI007 driver shim conformance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `80bfa19c692f23ff23d2817095f7bb2a6be89640bdeaccfcefc0a0f85dd2184b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80bfa19c692f23ff23d2817095f7bb2a6be89640bdeaccfcefc0a0f85dd2184b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80bfa19c692f23ff23d2817095f7bb2a6be89640bdeaccfcefc0a0f85dd2184b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/semantics/sffi_driver_shim_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/sffi_driver_shim_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/sffi_driver_shim_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/sffi_driver_shim_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/sffi_driver_shim_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/semantics/sffi_driver_shim_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors when a @driver module has extern functions but no Driver impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/sffi_driver_shim_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes when the @driver extern shim has a Driver impl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/sffi_driver_shim_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores modules without extern driver shims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
