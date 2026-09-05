# Opencl Session Readback Evidence Specification

> Tests covering OpenClSession readback evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencl Session Readback Evidence Specification

## Scenarios

### OpenClSession readback evidence

#### reports readback outcomes without claiming unverified OpenCL execution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports readback outcomes without claiming unverified OpenCL execution
   - Expected: matched.status_code equals `readback-matched`
   - Expected: matched.reason equals `readback-checksum-matched`
   - Expected: unavailable.success is false
   - Expected: unavailable.status_code equals `readback-unavailable`
   - Expected: mismatch.status_code equals `readback-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports readback outcomes without claiming unverified OpenCL execution")
val session = OpenClSession.create()
val matched = session.readback_evidence(true, 1234, 1234)
val unavailable = session.readback_evidence(false, 1234, 1234)
val mismatch = session.readback_evidence(true, 1234, 999)

expect(matched.status_code).to_equal("readback-matched")
expect(matched.reason).to_equal("readback-checksum-matched")
expect(unavailable.success).to_equal(false)
expect(unavailable.status_code).to_equal("readback-unavailable")
expect(mismatch.status_code).to_equal("readback-mismatch")
```

</details>

#### records typed buffer readback failures before checksum validation

- records typed buffer readback failures before checksum validation
   - Expected: missing_ffi.status_code equals `missing-ffi`
   - Expected: missing_queue.status_code equals `missing-queue`
   - Expected: missing_buffer.status_code equals `missing-buffer`
   - Expected: missing_host.status_code equals `missing-host-buffer`
   - Expected: invalid_size.status_code equals `invalid-size`
   - Expected: readback_failed.status_code equals `readback-failed`
   - Expected: readback_failed.reason equals `opencl-buffer-read-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records typed buffer readback failures before checksum validation")
val missing_ffi = OpenClSession.create().read_buffer_evidence(1, 1, 16, 1234, 1234)
var session = OpenClSession.create_with_ffi(OpenClFfi.create_static())
val missing_queue = session.read_buffer_evidence(1, 1, 16, 1234, 1234)
session.queue = 3
val missing_buffer = session.read_buffer_evidence(0, 1, 16, 1234, 1234)
val missing_host = session.read_buffer_evidence(1, 0, 16, 1234, 1234)
val invalid_size = session.read_buffer_evidence(1, 1, 0, 1234, 1234)
val readback_failed = session.read_buffer_evidence(1, 1, 16, 1234, 999)

expect(missing_ffi.status_code).to_equal("missing-ffi")
expect(missing_queue.status_code).to_equal("missing-queue")
expect(missing_buffer.status_code).to_equal("missing-buffer")
expect(missing_host.status_code).to_equal("missing-host-buffer")
expect(invalid_size.status_code).to_equal("invalid-size")
expect(readback_failed.status_code).to_equal("readback-failed")
expect(readback_failed.reason).to_equal("opencl-buffer-read-failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OpenClSession readback evidence.
- OpenClSession readback evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `e9927569cd90da1b1f1b76971794c1b2dc6ec518b5af41be28e43452659791d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9927569cd90da1b1f1b76971794c1b2dc6ec518b5af41be28e43452659791d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9927569cd90da1b1f1b76971794c1b2dc6ec518b5af41be28e43452659791d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
