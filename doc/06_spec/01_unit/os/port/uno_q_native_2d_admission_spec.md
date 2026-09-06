# Uno Q Native 2d Admission Specification

> Tests covering UNO Q QRB2210 native 2D admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Uno Q Native 2d Admission Specification

## Scenarios

### UNO Q QRB2210 native 2D admission

#### keeps complete evidence blocked while the canonical QRB2210 port is unavailable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps complete evidence blocked while the canonical QRB2210 port is unavailable
   - Expected: result.status equals `blocked`
   - Expected: result.reason equals `qrb2210-simpleos-port-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps complete evidence blocked while the canonical QRB2210 port is unavailable")
val result = uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 2, 4, true, true))
expect(result.status).to_equal("blocked")
expect(result.reason).to_equal("qrb2210-simpleos-port-unavailable")
```

</details>

#### classifies shipped Debian execution as readiness only

- classifies shipped Debian execution as readiness only
   - Expected: result.status equals `ready`
   - Expected: result.reason equals `vendor-os-readiness-is-not-simpleos-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("classifies shipped Debian execution as readiness only")
val result = uno_q_native_2d_admission(evidence("debian", "qrb2210-uno-q", false, 2, 4, true, true))
expect(result.status).to_equal("ready")
expect(result.reason).to_equal("vendor-os-readiness-is-not-simpleos-evidence")
```

</details>

#### rejects the STM32U585 coprocessor as a desktop target

- rejects the STM32U585 coprocessor as a desktop target
   - Expected: uno_q_native_2d_admission(evidence("simpleos", "stm32u585-uno-q", false, 2, 4, true, true)).reason equals `wrong-board-or-stm32-coprocessor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects the STM32U585 coprocessor as a desktop target")
expect(uno_q_native_2d_admission(evidence("simpleos", "stm32u585-uno-q", false, 2, 4, true, true)).reason).to_equal("wrong-board-or-stm32-coprocessor")
```

</details>

#### rejects any CPU fallback even with matching pixels

- rejects any CPU fallback even with matching pixels
   - Expected: uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", true, 2, 4, true, true)).reason equals `device-execution-or-no-fallback-not-proven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects any CPU fallback even with matching pixels")
expect(uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", true, 2, 4, true, true)).reason).to_equal("device-execution-or-no-fallback-not-proven")
```

</details>

#### rejects a receipt without animation or font work

- rejects a receipt without animation or font work
   - Expected: uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 1, 0, true, true)).reason equals `drawir-vulkan-route-not-proven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a receipt without animation or font work")
expect(uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 1, 0, true, true)).reason).to_equal("drawir-vulkan-route-not-proven")
```

</details>

#### rejects missing ordinary keyboard delivery

- rejects missing ordinary keyboard delivery
   - Expected: uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 2, 4, false, true)).reason equals `input-receipts-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects missing ordinary keyboard delivery")
expect(uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 2, 4, false, true)).reason).to_equal("input-receipts-incomplete")
```

</details>

#### rejects silent audio completion

- rejects silent audio completion
   - Expected: uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 2, 4, true, false)).reason equals `audio-completion-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects silent audio completion")
expect(uno_q_native_2d_admission(evidence("simpleos", "qrb2210-uno-q", false, 2, 4, true, false)).reason).to_equal("audio-completion-incomplete")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/uno_q_native_2d_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UNO Q QRB2210 native 2D admission.
- UNO Q QRB2210 native 2D admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1dff87a65a55d0b391554e65459852e60982347555ff17345bdbc461a160e580`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1dff87a65a55d0b391554e65459852e60982347555ff17345bdbc461a160e580`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1dff87a65a55d0b391554e65459852e60982347555ff17345bdbc461a160e580`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/os/port/uno_q_native_2d_admission_spec.spl
mirror: doc/06_spec/01_unit/os/port/uno_q_native_2d_admission_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/uno_q_native_2d_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/uno_q_native_2d_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
