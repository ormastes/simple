# Model Loader Stream Plan Specification

> Tests covering Slang tensor stream plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Stream Plan Specification

## Scenarios

### Slang tensor stream plan

#### builds a plan-only single-segment read plan for one chunk

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a plan-only single-segment read plan for one chunk
   - Expected: stream_plan_status(root, name) equals `ok`
   - Expected: stream_plan_execution_status(root, name) equals `plan_only_not_scheduled`
   - Expected: stream_plan_total_bytes(root, name) equals `16`
   - Expected: stream_plan_segment_count(root, name) equals `1`
   - Expected: stream_plan_segment_path(root, name, 0) equals `data-000.bin`
   - Expected: stream_plan_segment_offset(root, name, 0) equals `0`
   - Expected: stream_plan_segment_bytes(root, name, 0) equals `16`
   - Expected: stream_plan_segment_tensor_offset(root, name, 0) equals `0`
   - Expected: stream_plan_pin_requested(root, name) is true
   - Expected: stream_plan_device_staging_requested(root, name) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a plan-only single-segment read plan for one chunk")
val root = "test/fixtures/slang/valid_pack"
val name = "tok_embeddings.weight"
expect(stream_plan_status(root, name)).to_equal("ok")
expect(stream_plan_execution_status(root, name)).to_equal("plan_only_not_scheduled")
expect(stream_plan_total_bytes(root, name)).to_equal(16)
expect(stream_plan_segment_count(root, name)).to_equal(1)
expect(stream_plan_segment_path(root, name, 0)).to_equal("data-000.bin")
expect(stream_plan_segment_offset(root, name, 0)).to_equal(0)
expect(stream_plan_segment_bytes(root, name, 0)).to_equal(16)
expect(stream_plan_segment_tensor_offset(root, name, 0)).to_equal(0)
expect(stream_plan_pin_requested(root, name)).to_equal(true)
expect(stream_plan_device_staging_requested(root, name)).to_equal(true)
```

</details>

#### splits a cross-chunk tensor span into ordered read segments

- splits a cross-chunk tensor span into ordered read segments
   - Expected: stream_plan_status(root, name) equals `ok`
   - Expected: stream_plan_total_bytes(root, name) equals `7`
   - Expected: stream_plan_segment_count(root, name) equals `2`
   - Expected: stream_plan_segment_path(root, name, 0) equals `data-000.bin`
   - Expected: stream_plan_segment_offset(root, name, 0) equals `1`
   - Expected: stream_plan_segment_bytes(root, name, 0) equals `4`
   - Expected: stream_plan_segment_tensor_offset(root, name, 0) equals `0`
   - Expected: stream_plan_segment_path(root, name, 1) equals `data-001.bin`
   - Expected: stream_plan_segment_offset(root, name, 1) equals `0`
   - Expected: stream_plan_segment_bytes(root, name, 1) equals `3`
   - Expected: stream_plan_segment_tensor_offset(root, name, 1) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits a cross-chunk tensor span into ordered read segments")
val root = "test/fixtures/slang/cross_chunk_pack"
val name = "split.weight"
expect(stream_plan_status(root, name)).to_equal("ok")
expect(stream_plan_total_bytes(root, name)).to_equal(7)
expect(stream_plan_segment_count(root, name)).to_equal(2)
expect(stream_plan_segment_path(root, name, 0)).to_equal("data-000.bin")
expect(stream_plan_segment_offset(root, name, 0)).to_equal(1)
expect(stream_plan_segment_bytes(root, name, 0)).to_equal(4)
expect(stream_plan_segment_tensor_offset(root, name, 0)).to_equal(0)
expect(stream_plan_segment_path(root, name, 1)).to_equal("data-001.bin")
expect(stream_plan_segment_offset(root, name, 1)).to_equal(0)
expect(stream_plan_segment_bytes(root, name, 1)).to_equal(3)
expect(stream_plan_segment_tensor_offset(root, name, 1)).to_equal(4)
```

</details>

#### reports missing tensor names without returning a plan

- reports missing tensor names without returning a plan
   - Expected: stream_plan_status("test/fixtures/slang/valid_pack", "missing.weight") equals `tensor_not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing tensor names without returning a plan")
expect(stream_plan_status("test/fixtures/slang/valid_pack", "missing.weight")).to_equal("tensor_not_found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Slang tensor stream plan.
- Slang tensor stream plan

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

- Canonical SPipe generation for source `1ce6cf8d92cf057b026b9a425526dee86533ca966531afaad08b3b70258878ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ce6cf8d92cf057b026b9a425526dee86533ca966531afaad08b3b70258878ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ce6cf8d92cf057b026b9a425526dee86533ca966531afaad08b3b70258878ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a plan-only single-segment read plan for one chunk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits a cross-chunk tensor span into ordered read segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_loader_stream_plan_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing tensor names without returning a plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
