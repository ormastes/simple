# Model Loader Streaming Readiness Specification

> Tests covering Slang streaming readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Streaming Readiness Specification

## Scenarios

### Slang streaming readiness

#### blocks full streaming when native read_range support is unavailable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks full streaming when native read_range support is unavailable
   - Expected: readiness.status equals `blocked`
   - Expected: readiness.reason equals `native_read_range_unavailable`
   - Expected: readiness.plan_status equals `ok`
   - Expected: readiness.execution_status equals `plan_only_not_scheduled`
   - Expected: readiness.read_range_status equals `unsupported`
   - Expected: readiness.pinned_buffer_status equals `unsupported`
   - Expected: readiness.device_staging_status equals `unsupported`
   - Expected: readiness.local_read_bytes_status equals `unchecked`
   - Expected: readiness.segment_count equals `1`
   - Expected: readiness.total_byte_len equals `16`
   - Expected: readiness.evidence_jsonl does not contain `absence_marker()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks full streaming when native read_range support is unavailable")
val readiness = slang_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "tok_embeddings.weight", "unsupported", "unsupported", "unsupported")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("native_read_range_unavailable")
expect(readiness.plan_status).to_equal("ok")
expect(readiness.execution_status).to_equal("plan_only_not_scheduled")
expect(readiness.read_range_status).to_equal("unsupported")
expect(readiness.pinned_buffer_status).to_equal("unsupported")
expect(readiness.device_staging_status).to_equal("unsupported")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.segment_count).to_equal(1)
expect(readiness.total_byte_len).to_equal(16)
expect(readiness.evidence_jsonl).to_contain("\"event\":\"slang_streaming_readiness\"")
expect(readiness.evidence_jsonl).to_contain("\"status\":\"blocked\"")
expect(readiness.evidence_jsonl).to_contain("\"read_range\":\"unsupported\"")
expect(readiness.evidence_jsonl.contains(absence_marker())).to_equal(false)
```

</details>

#### reports ready only when every native streaming capability is ready

- reports ready only when every native streaming capability is ready
   - Expected: readiness.status equals `ready`
   - Expected: readiness.reason equals `ready`
   - Expected: readiness.plan_status equals `ok`
   - Expected: readiness.execution_status equals `ready_to_schedule`
   - Expected: readiness.local_read_bytes_status equals `unchecked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports ready only when every native streaming capability is ready")
val readiness = slang_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "tok_embeddings.weight", "ready", "ready", "ready")

expect(readiness.status).to_equal("ready")
expect(readiness.reason).to_equal("ready")
expect(readiness.plan_status).to_equal("ok")
expect(readiness.execution_status).to_equal("ready_to_schedule")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.evidence_jsonl).to_contain("\"status\":\"ready\"")
expect(readiness.evidence_jsonl).to_contain("\"execution_status\":\"ready_to_schedule\"")
```

</details>

#### reports local byte reads ready without claiming native pinned streaming

- reports local byte reads ready without claiming native pinned streaming
   - Expected: readiness.status equals `blocked`
   - Expected: readiness.reason equals `native_read_range_unavailable`
   - Expected: readiness.plan_status equals `ok`
   - Expected: readiness.execution_status equals `local_read_bytes_ready`
   - Expected: readiness.read_range_status equals `unsupported`
   - Expected: readiness.pinned_buffer_status equals `unsupported`
   - Expected: readiness.device_staging_status equals `unsupported`
   - Expected: readiness.local_read_bytes_status equals `ready`
   - Expected: readiness.segment_count equals `1`
   - Expected: readiness.total_byte_len equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports local byte reads ready without claiming native pinned streaming")
val readiness = slang_streaming_readiness_from_local_pack("test/fixtures/slang/valid_pack", "tok_embeddings.weight")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("native_read_range_unavailable")
expect(readiness.plan_status).to_equal("ok")
expect(readiness.execution_status).to_equal("local_read_bytes_ready")
expect(readiness.read_range_status).to_equal("unsupported")
expect(readiness.pinned_buffer_status).to_equal("unsupported")
expect(readiness.device_staging_status).to_equal("unsupported")
expect(readiness.local_read_bytes_status).to_equal("ready")
expect(readiness.segment_count).to_equal(1)
expect(readiness.total_byte_len).to_equal(16)
expect(readiness.evidence_jsonl).to_contain("\"local_read_bytes\":\"ready\"")
```

</details>

#### keeps loader failures distinct from native capability gaps

- keeps loader failures distinct from native capability gaps
   - Expected: readiness.status equals `blocked`
   - Expected: readiness.reason equals `tensor_not_found`
   - Expected: readiness.plan_status equals `error`
   - Expected: readiness.local_read_bytes_status equals `unchecked`
   - Expected: readiness.segment_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps loader failures distinct from native capability gaps")
val readiness = slang_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "missing.weight", "unsupported", "unsupported", "unsupported")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("tensor_not_found")
expect(readiness.plan_status).to_equal("error")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.segment_count).to_equal(0)
expect(readiness.evidence_jsonl).to_contain("\"reason\":\"tensor_not_found\"")
```

</details>

#### normalizes unknown native capability statuses in evidence

- normalizes unknown native capability statuses in evidence
   - Expected: readiness.status equals `blocked`
   - Expected: readiness.reason equals `pinned_buffer_registration_unavailable`
   - Expected: readiness.read_range_status equals `ready`
   - Expected: readiness.pinned_buffer_status equals `unavailable`
   - Expected: readiness.device_staging_status equals `unchecked`
   - Expected: readiness.local_read_bytes_status equals `unchecked`
   - Expected: readiness.evidence_jsonl does not contain `maybe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes unknown native capability statuses in evidence")
val readiness = slang_streaming_readiness_from_manifest_text("/tmp/pack", one_tensor_manifest(), "tok_embeddings.weight", "ready", "maybe\\\"bad", "unchecked")

expect(readiness.status).to_equal("blocked")
expect(readiness.reason).to_equal("pinned_buffer_registration_unavailable")
expect(readiness.read_range_status).to_equal("ready")
expect(readiness.pinned_buffer_status).to_equal("unavailable")
expect(readiness.device_staging_status).to_equal("unchecked")
expect(readiness.local_read_bytes_status).to_equal("unchecked")
expect(readiness.evidence_jsonl).to_contain("\"pinned_buffer\":\"unavailable\"")
expect(readiness.evidence_jsonl.contains("maybe")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Slang streaming readiness.
- Slang streaming readiness

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

- Canonical SPipe generation for source `84cc4c65feaf9ce04aa5fb3a12bdcef27284a3c3e33ecb07d76424a3c5347a07`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84cc4c65feaf9ce04aa5fb3a12bdcef27284a3c3e33ecb07d76424a3c5347a07`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84cc4c65feaf9ce04aa5fb3a12bdcef27284a3c3e33ecb07d76424a3c5347a07`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks full streaming when native read_range support is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports ready only when every native streaming capability is ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_loader_streaming_readiness_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports local byte reads ready without claiming native pinned streaming' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
