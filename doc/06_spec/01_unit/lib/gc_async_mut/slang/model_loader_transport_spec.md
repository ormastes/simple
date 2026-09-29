# Model Loader Transport Specification

> Tests covering Slang memory NVFS streaming transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Transport Specification

## Scenarios

### Slang memory NVFS streaming transport

#### streams a manifest and chunk bytes through the restored loader entry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- streams a manifest and chunk bytes through the restored loader entry
   - Expected: streamed_status(manifest_one_chunk(), chunks) equals `tiny:1:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streams a manifest and chunk bytes through the restored loader entry")
var chunks: [[u8]] = []
chunks.push(bytes4())
expect(streamed_status(manifest_one_chunk(), chunks)).to_equal("tiny:1:1")
```

</details>

#### streams a pack image through the memory NVFS transport

- streams a pack image through the memory NVFS transport
   - Expected: via_status(manifest_one_chunk(), paths, chunks) equals `tiny:1:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streams a pack image through the memory NVFS transport")
var paths: [text] = []
paths.push("data-000.bin")
var chunks: [[u8]] = []
chunks.push(bytes4())
expect(via_status(manifest_one_chunk(), paths, chunks)).to_equal("tiny:1:1")
```

</details>

#### maps missing transport chunks to chunk_error

- maps missing transport chunks to chunk_error
   - Expected: via_status(manifest_one_chunk(), paths, chunks) equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps missing transport chunks to chunk_error")
var paths: [text] = []
paths.push("other.bin")
var chunks: [[u8]] = []
chunks.push(bytes4())
expect(via_status(manifest_one_chunk(), paths, chunks)).to_equal("chunk_error")
```

</details>

#### maps short streamed chunk data to chunk_error

- maps short streamed chunk data to chunk_error
   - Expected: streamed_status(manifest_one_chunk(), chunks) equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps short streamed chunk data to chunk_error")
var chunks: [[u8]] = []
chunks.push(bytes2(0x10 as u8, 0x20 as u8))
expect(streamed_status(manifest_one_chunk(), chunks)).to_equal("chunk_error")
```

</details>

#### validates split tensor chunks through the streamed path

- validates split tensor chunks through the streamed path
   - Expected: streamed_status(manifest_two_chunks(), chunks) equals `tiny:2:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates split tensor chunks through the streamed path")
var chunks: [[u8]] = []
chunks.push(bytes2(0x10 as u8, 0x20 as u8))
chunks.push(bytes2(0x30 as u8, 0x40 as u8))
expect(streamed_status(manifest_two_chunks(), chunks)).to_equal("tiny:2:1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Slang memory NVFS streaming transport.
- Slang memory NVFS streaming transport

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

- Canonical SPipe generation for source `e7370ae26d1224d5045381937c5f40616bdda5a5dbf75456f85575958f3b2aa7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7370ae26d1224d5045381937c5f40616bdda5a5dbf75456f85575958f3b2aa7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7370ae26d1224d5045381937c5f40616bdda5a5dbf75456f85575958f3b2aa7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'streams a manifest and chunk bytes through the restored loader entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'streams a pack image through the memory NVFS transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_loader_transport_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps missing transport chunks to chunk_error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
