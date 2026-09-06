# Wm Production Acceptance Specification

> Tests covering production WM acceptance contract fixtures.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Production Acceptance Specification

## Scenarios

### production WM acceptance contract fixtures

#### defines deterministic architecture profiles without claiming readiness

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines deterministic architecture profiles without claiming readiness
   - Expected: wm_acceptance_target_v1("x86_64").input_class equals `physical-visible-window`
   - Expected: wm_acceptance_target_v1("aarch64").capture_source equals `qmp-ramfb-screendump`
   - Expected: wm_acceptance_target_v1("riscv64").machine equals `virt`
   - Expected: wm_acceptance_target_v1("arm32").machine equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines deterministic architecture profiles without claiming readiness")
expect(wm_acceptance_target_v1("x86_64").input_class).to_equal("physical-visible-window")
expect(wm_acceptance_target_v1("aarch64").capture_source).to_equal("qmp-ramfb-screendump")
expect(wm_acceptance_target_v1("riscv64").machine).to_equal("virt")
expect(wm_acceptance_target_v1("arm32").machine).to_equal("")
```

</details>

#### admits structurally complete contract fixtures for all declared architectures

- admits structurally complete contract fixtures for all declared architectures
   - Expected: wm_production_acceptance_admit_v1(candidate("x86_64")).reason equals `accepted`
   - Expected: wm_production_acceptance_admit_v1(candidate("aarch64")).reason equals `accepted`
   - Expected: wm_production_acceptance_admit_v1(candidate("riscv64")).reason equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits structurally complete contract fixtures for all declared architectures")
expect(wm_production_acceptance_admit_v1(candidate("x86_64")).reason).to_equal("accepted")
expect(wm_production_acceptance_admit_v1(candidate("aarch64")).reason).to_equal("accepted")
expect(wm_production_acceptance_admit_v1(candidate("riscv64")).reason).to_equal("accepted")
```

</details>

#### rejects event reordering and diagnostic input mislabeled as physical

- rejects event reordering and diagnostic input mislabeled as physical
   - Expected: wm_production_acceptance_admit_v1(reordered).reason equals `event-sequence-mismatch`
   - Expected: wm_production_acceptance_admit_v1(mislabeled).reason equals `diagnostic-input-mislabeled-physical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects event reordering and diagnostic input mislabeled as physical")
var reordered = candidate("x86_64")
reordered.events.sequence = "focus,pointer_down,pointer_move"
expect(wm_production_acceptance_admit_v1(reordered).reason).to_equal("event-sequence-mismatch")
var mislabeled = candidate("aarch64")
mislabeled.events.physical_input_attested = true
expect(wm_production_acceptance_admit_v1(mislabeled).reason).to_equal("diagnostic-input-mislabeled-physical")
```

</details>

#### rejects unchanged captures and uncorrelated presentation revisions

- rejects unchanged captures and uncorrelated presentation revisions
   - Expected: wm_production_acceptance_admit_v1(unchanged).reason equals `capture-checksum-not-changed`
   - Expected: wm_production_acceptance_admit_v1(stale).reason equals `event-presentation-correlation-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unchanged captures and uncorrelated presentation revisions")
var unchanged = candidate("aarch64")
unchanged.capture.after_checksum = unchanged.capture.before_checksum
expect(wm_production_acceptance_admit_v1(unchanged).reason).to_equal("capture-checksum-not-changed")
var stale = candidate("aarch64")
stale.events.presented_revision = 11u64
expect(wm_production_acceptance_admit_v1(stale).reason).to_equal("event-presentation-correlation-invalid")
```

</details>

#### rejects unbounded samples latency heap growth fallback and incomplete cleanup

- rejects unbounded samples latency heap growth fallback and incomplete cleanup
   - Expected: wm_production_acceptance_admit_v1(samples).reason equals `frame-sample-bound-invalid`
   - Expected: wm_production_acceptance_admit_v1(latency).reason equals `frame-latency-budget-exceeded`
   - Expected: wm_production_acceptance_admit_v1(heap).reason equals `guest-heap-budget-exceeded`
   - Expected: wm_production_acceptance_admit_v1(fallback).reason equals `fallback-forbidden`
   - Expected: wm_production_acceptance_admit_v1(orphan).reason equals `cleanup-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unbounded samples latency heap growth fallback and incomplete cleanup")
var samples = candidate("riscv64")
samples.performance.measured_frames = 257
expect(wm_production_acceptance_admit_v1(samples).reason).to_equal("frame-sample-bound-invalid")
var latency = candidate("riscv64")
latency.performance.frame_p95_us = 33401
expect(wm_production_acceptance_admit_v1(latency).reason).to_equal("frame-latency-budget-exceeded")
var heap = candidate("riscv64")
heap.performance.guest_heap_delta_bytes = 1
expect(wm_production_acceptance_admit_v1(heap).reason).to_equal("guest-heap-budget-exceeded")
var fallback = candidate("riscv64")
fallback.fallback_used = true
expect(wm_production_acceptance_admit_v1(fallback).reason).to_equal("fallback-forbidden")
var orphan = candidate("riscv64")
orphan.orphan_process_count = 1
expect(wm_production_acceptance_admit_v1(orphan).reason).to_equal("cleanup-incomplete")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_production_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering production WM acceptance contract fixtures.
- production WM acceptance contract fixtures

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c29411e3324d11b459d398cfb17ff87b53a08957a62a92e5a2b0e40deee9a0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c29411e3324d11b459d398cfb17ff87b53a08957a62a92e5a2b0e40deee9a0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c29411e3324d11b459d398cfb17ff87b53a08957a62a92e5a2b0e40deee9a0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/wm_production_acceptance_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_production_acceptance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/wm_production_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_production_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/wm_production_acceptance_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits structurally complete contract fixtures for all declared architectures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_production_acceptance_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects event reordering and diagnostic input mislabeled as physical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_production_acceptance_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unchanged captures and uncorrelated presentation revisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
