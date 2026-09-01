# Host Service Contract Specification

> Tests covering SOSIX host-service contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Service Contract Specification

## Scenarios

### SOSIX host-service contracts

#### snapshots startup configuration as typed values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- snapshots startup configuration as typed values
   - Expected: snapshot.display_backend equals `headless`
   - Expected: snapshot.storage_root equals `/mnt/data/.simple`
   - Expected: snapshot.evidence_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("snapshots startup configuration as typed values")
val snapshot = sosix_host_configuration_snapshot_create("headless", "queue", "cpu", true, "/mnt/data/.simple")
expect(snapshot.display_backend).to_equal("headless")
expect(snapshot.storage_root).to_equal("/mnt/data/.simple")
expect(snapshot.evidence_enabled).to_equal(true)
```

</details>

#### accepts one batched display frame identity

- accepts one batched display frame identity
   - Expected: result.accepted is true
   - Expected: result.request.surface_generation equals `3`
   - Expected: result.request.frame_sequence equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts one batched display frame identity")
val result = sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, capability(), 3, 44, buffer(), 1000)
expect(result.accepted).to_equal(true)
expect(result.request.surface_generation).to_equal(3)
expect(result.request.frame_sequence).to_equal(44)
```

</details>

#### rejects invalid display API surface buffer and sequence

- rejects invalid display API surface buffer and sequence
   - Expected: sosix_display_request_create(operation(), 99, capability(), 1, 1, buffer(), 0).reason equals `unsupported-display-api`
   - Expected: sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, bad_cap, 1, 1, buffer(), 0).reason equals `invalid-surface`
   - Expected: sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, capability(), 1, 1, bad_buf, 0).reason equals `invalid-frame-buffer`
   - Expected: sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, capability(), 1, 0, buffer(), 0).reason equals `invalid-frame-sequence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects invalid display API surface buffer and sequence")
val bad_cap = SosixCapabilityRef(slot: 4, generation: 0)
val bad_buf = SosixBufferRef(slot: 5, generation: 0)
expect(sosix_display_request_create(operation(), 99, capability(), 1, 1, buffer(), 0).reason).to_equal("unsupported-display-api")
expect(sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, bad_cap, 1, 1, buffer(), 0).reason).to_equal("invalid-surface")
expect(sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, capability(), 1, 1, bad_buf, 0).reason).to_equal("invalid-frame-buffer")
expect(sosix_display_request_create(operation(), SOSIX_HOST_DISPLAY_PRESENT, capability(), 1, 0, buffer(), 0).reason).to_equal("invalid-frame-sequence")
```

</details>

#### rejects stale surface and frame completion identities

- rejects stale surface and frame completion identities
   - Expected: sosix_display_completion_matches(expected, exact) is true
   - Expected: sosix_display_completion_matches(expected, stale) is false
   - Expected: sosix_display_completion_matches(expected, wrong_frame) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects stale surface and frame completion identities")
val expected = SosixDisplayCompletionKey(surface: capability(), surface_generation: 8, frame_sequence: 21)
val exact = SosixDisplayCompletionKey(surface: capability(), surface_generation: 8, frame_sequence: 21)
val stale = SosixDisplayCompletionKey(surface: capability(), surface_generation: 7, frame_sequence: 21)
val wrong_frame = SosixDisplayCompletionKey(surface: capability(), surface_generation: 8, frame_sequence: 20)
expect(sosix_display_completion_matches(expected, exact)).to_equal(true)
expect(sosix_display_completion_matches(expected, stale)).to_equal(false)
expect(sosix_display_completion_matches(expected, wrong_frame)).to_equal(false)
```

</details>

#### validates input stream generation

- validates input stream generation
   - Expected: sosix_input_request_create(operation(), capability(), 17, 2000).accepted is true
   - Expected: sosix_input_request_create(operation(), invalid, 17, 2000).reason equals `invalid-input-stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("validates input stream generation")
expect(sosix_input_request_create(operation(), capability(), 17, 2000).accepted).to_equal(true)
val invalid = SosixCapabilityRef(slot: 4, generation: 0)
expect(sosix_input_request_create(operation(), invalid, 17, 2000).reason).to_equal("invalid-input-stream")
```

</details>

#### requires a valid timer and nonzero deadline

- requires a valid timer and nonzero deadline
   - Expected: sosix_timer_request_create(operation(), capability(), 2000).accepted is true
   - Expected: sosix_timer_request_create(operation(), invalid, 2000).reason equals `invalid-timer`
   - Expected: sosix_timer_request_create(operation(), capability(), 0).reason equals `missing-deadline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires a valid timer and nonzero deadline")
expect(sosix_timer_request_create(operation(), capability(), 2000).accepted).to_equal(true)
val invalid = SosixCapabilityRef(slot: 4, generation: 0)
expect(sosix_timer_request_create(operation(), invalid, 2000).reason).to_equal("invalid-timer")
expect(sosix_timer_request_create(operation(), capability(), 0).reason).to_equal("missing-deadline")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/host_service_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX host-service contracts.
- SOSIX host-service contracts

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5491ba579d750e85036aabec710b6caa6454cf183311d9d936c0bbc6c5ece7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5491ba579d750e85036aabec710b6caa6454cf183311d9d936c0bbc6c5ece7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5491ba579d750e85036aabec710b6caa6454cf183311d9d936c0bbc6c5ece7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/sosix/host_service_contract_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/host_service_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/host_service_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/host_service_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/host_service_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/host_service_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshots startup configuration as typed values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/host_service_contract_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts one batched display frame identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/host_service_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid display API surface buffer and sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
