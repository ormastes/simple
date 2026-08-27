# Provider Loader Evidence Binding Class Specification

> Tests covering admission evidence must be bound to the object it describes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Loader Evidence Binding Class Specification

## Scenarios

### admission evidence must be bound to the object it describes

#### finds admission entry points to check

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds admission entry points to check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds admission entry points to check")
val src = loader_source()
expect(src.len() > 0).to_be(true)
val names = fn_names(src)
var admitters = 0
var i = 0
while i < names.len():
    if is_admission_entry(names[i]):
        admitters = admitters + 1
    i = i + 1
expect(admitters > 0).to_be(true)
```

</details>

#### every admission entry point that reads a path and re-opens it re-verifies after open

- every admission entry point that reads a path and re-opens it re-verifies after open


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every admission entry point that reads a path and re-opens it re-verifies after open")
val src = loader_source()
val names = fn_names(src)
val bodies = fn_bodies(src)
var offenders: [text] = []
var checked = 0
var i = 0
while i < names.len() and i < bodies.len():
    if is_admission_entry(names[i]):
        val body = bodies[i]
        if reads_a_path(body) and reopens_a_path(body):
            checked = checked + 1
            if not rebinds_after_open(body):
                offenders.push(names[i])
    i = i + 1
expect(checked > 0).to_be(true)
expect(offenders.len()).to_be(0)
```

</details>

#### the fail-closed status is a distinct, exported admission status

- the fail-closed status is a distinct, exported admission status


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the fail-closed status is a distinct, exported admission status")
val src = loader_source()
expect(src.contains("val PROVIDER_ADMISSION_DIGEST_UNSTABLE")).to_be(true)
expect(src.contains("export PROVIDER_ADMISSION_DIGEST_UNSTABLE") or
    src.contains("PROVIDER_ADMISSION_DIGEST_UNSTABLE,")).to_be(true)
```

</details>

#### the fail-closed status is not aliased onto OK

- the fail-closed status is not aliased onto OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the fail-closed status is not aliased onto OK")
val src = loader_source()
val decl = src.split("val PROVIDER_ADMISSION_DIGEST_UNSTABLE: i32 = ")
expect(decl.len() > 1).to_be(true)
val value = decl[1].split("\n")[0]
expect(value == "0").to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/smf/provider_loader_evidence_binding_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering admission evidence must be bound to the object it describes.
- admission evidence must be bound to the object it describes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `c0d4fcd67aae86cec140a8eb58b4513b10dfd36fd5f9868c5d09c8c418aa9f7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0d4fcd67aae86cec140a8eb58b4513b10dfd36fd5f9868c5d09c8c418aa9f7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0d4fcd67aae86cec140a8eb58b4513b10dfd36fd5f9868c5d09c8c418aa9f7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/smf/provider_loader_evidence_binding_class_spec.spl
mirror: doc/06_spec/01_unit/os/smf/provider_loader_evidence_binding_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smf/provider_loader_evidence_binding_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smf/provider_loader_evidence_binding_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/smf/provider_loader_evidence_binding_class_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds admission entry points to check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smf/provider_loader_evidence_binding_class_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every admission entry point that reads a path and re-opens it re-verifies after open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smf/provider_loader_evidence_binding_class_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the fail-closed status is a distinct, exported admission status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
