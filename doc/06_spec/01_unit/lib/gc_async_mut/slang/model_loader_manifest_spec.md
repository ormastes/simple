# Model Loader Manifest Specification

> Tests covering Slang tensor-pack manifest loader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Manifest Specification

## Scenarios

### Slang tensor-pack manifest loader

#### parses canonical empty v0 manifest text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses canonical empty v0 manifest text
   - Expected: manifest_status(empty_manifest()) equals `ok`
   - Expected: manifest_model_id(empty_manifest()) equals `tiny`
   - Expected: manifest_counts(empty_manifest()) equals `0:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses canonical empty v0 manifest text")
expect(manifest_status(empty_manifest())).to_equal("ok")
expect(manifest_model_id(empty_manifest())).to_equal("tiny")
expect(manifest_counts(empty_manifest())).to_equal("0:0")
```

</details>

#### rejects malformed and unsupported manifests

- rejects malformed and unsupported manifests
   - Expected: manifest_status("not a manifest") equals `error`
   - Expected: manifest_status("{\"schema_version\":1,\"model_id\":\"tiny\",\"revision\":\"r1\",\"preferred_chunk_bytes\":4096,\"chunks\":[],\"tensors\":[]}") equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed and unsupported manifests")
expect(manifest_status("not a manifest")).to_equal("error")
expect(manifest_status("{\"schema_version\":1,\"model_id\":\"tiny\",\"revision\":\"r1\",\"preferred_chunk_bytes\":4096,\"chunks\":[],\"tensors\":[]}")).to_equal("error")
```

</details>

#### loads an already-read empty manifest without throwing

- loads an already-read empty manifest without throwing
   - Expected: load_status("/tmp/pack", empty_manifest()) equals `ok`
   - Expected: load_status("", empty_manifest()) equals `error`
   - Expected: pack_load_status("/tmp/pack") equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads an already-read empty manifest without throwing")
expect(load_status("/tmp/pack", empty_manifest())).to_equal("ok")
expect(load_status("", empty_manifest())).to_equal("error")
expect(pack_load_status("/tmp/pack")).to_equal("error")
```

</details>

#### materializes canonical non-empty tensor and chunk metadata

- materializes canonical non-empty tensor and chunk metadata
   - Expected: manifest_status(one_tensor_manifest()) equals `ok`
   - Expected: manifest_counts(one_tensor_manifest()) equals `1:1`
   - Expected: pack_summary("/tmp/pack", one_tensor_manifest()) equals `tiny:1:1:16`
   - Expected: manifest_status(bad_chunk_manifest()) equals `error`
   - Expected: manifest_status(bad_digest_manifest()) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("materializes canonical non-empty tensor and chunk metadata")
expect(manifest_status(one_tensor_manifest())).to_equal("ok")
expect(manifest_counts(one_tensor_manifest())).to_equal("1:1")
expect(pack_summary("/tmp/pack", one_tensor_manifest())).to_equal("tiny:1:1:16")
expect(manifest_status(bad_chunk_manifest())).to_equal("error")
expect(manifest_status(bad_digest_manifest())).to_equal("error")
```

</details>

#### loads manifest.sdn from a pack root

- loads manifest.sdn from a pack root
   - Expected: pack_load_status("test/fixtures/slang/valid_pack") equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads manifest.sdn from a pack root")
expect(pack_load_status("test/fixtures/slang/valid_pack")).to_equal("ok")
```

</details>

#### rejects missing chunk files from a pack root

- rejects missing chunk files from a pack root
   - Expected: pack_load_detail("test/fixtures/slang/missing_chunk_pack") equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing chunk files from a pack root")
expect(pack_load_detail("test/fixtures/slang/missing_chunk_pack")).to_equal("chunk_error")
```

</details>

#### rejects mismatched chunk files from a pack root

- rejects mismatched chunk files from a pack root
   - Expected: pack_load_detail("test/fixtures/slang/wrong_chunk_pack") equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects mismatched chunk files from a pack root")
expect(pack_load_detail("test/fixtures/slang/wrong_chunk_pack")).to_equal("chunk_error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Slang tensor-pack manifest loader.
- Slang tensor-pack manifest loader

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9674d4e141fe8b541b8adbd91b310db379993abcec1f7f1082a6b639316c375`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9674d4e141fe8b541b8adbd91b310db379993abcec1f7f1082a6b639316c375`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9674d4e141fe8b541b8adbd91b310db379993abcec1f7f1082a6b639316c375`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses canonical empty v0 manifest text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed and unsupported manifests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_loader_manifest_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads an already-read empty manifest without throwing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
