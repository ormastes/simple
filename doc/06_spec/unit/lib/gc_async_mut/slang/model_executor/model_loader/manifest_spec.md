# Manifest Specification

> Tests covering TensorPackManifest.empty, parse_manifest (A1 stub), build_tensor_pack (A1 stub), serialize_manifest (A2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manifest Specification

## Scenarios

### TensorPackManifest.empty

#### is_empty on fresh value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is_empty on fresh value
   - Expected: m.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_empty on fresh value")
val m = TensorPackManifest.empty()
expect(m.is_empty()).to_equal(true)
```

</details>

#### has schema_version 0

- has schema_version 0
   - Expected: m.schema_version equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has schema_version 0")
val m = TensorPackManifest.empty()
expect(m.schema_version).to_equal(0)
```

</details>

### parse_manifest (A1 stub)

#### rejects empty input

- rejects empty input
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty input")
val r = parse_manifest("")
expect(r.is_err()).to_equal(true)
```

</details>

#### TODO: returns Ok on a well-formed v0 manifest

- TODO: returns Ok on a well-formed v0 manifest
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TODO: returns Ok on a well-formed v0 manifest")
val sdn = "schema_version: 0\nmodel_id: \"demo\"\nrevision: \"v0\"\npreferred_chunk_bytes: 2097152\nchunks: []\ntensors: []\n"
val r = parse_manifest(sdn)
# Intentionally failing until the parser is implemented.
expect(r.is_ok()).to_equal(true)
```

</details>

### build_tensor_pack (A1 stub)

#### TODO: materialises a pack from a parsed manifest

- TODO: materialises a pack from a parsed manifest
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TODO: materialises a pack from a parsed manifest")
val m = TensorPackManifest.empty()
val r = build_tensor_pack("/tmp/pack", m)
# Intentionally failing until build is implemented.
expect(r.is_ok()).to_equal(true)
```

</details>

### serialize_manifest (A2)

#### produces non-empty bytes

- produces non-empty bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces non-empty bytes")
val pack = _demo_pack()
val out = serialize_manifest(pack)
expect(out.len()).to_be_greater_than(10)
```

</details>

#### includes the schema_version field

- includes the schema_version field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes the schema_version field")
val out = serialize_manifest(_demo_pack())
expect(out).to_contain("schema_version")
```

</details>

#### includes the tensor name 'w' and dtype F32

- includes the tensor name 'w' and dtype F32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes the tensor name 'w' and dtype F32")
val out = serialize_manifest(_demo_pack())
expect(out).to_contain("w")
expect(out).to_contain("F32")
```

</details>

#### includes digest_hex and relative_path

- includes digest_hex and relative_path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes digest_hex and relative_path")
val out = serialize_manifest(_demo_pack())
expect(out).to_contain("0011aabb")
expect(out).to_contain("data-000.bin")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TensorPackManifest.empty, parse_manifest (A1 stub), build_tensor_pack (A1 stub), serialize_manifest (A2).
- TensorPackManifest.empty
- parse_manifest (A1 stub)
- build_tensor_pack (A1 stub)
- serialize_manifest (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `5b72f61013ed13acae0442a107a91c51a39bcf19d7af0dc5850bbb2fb44aa10b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b72f61013ed13acae0442a107a91c51a39bcf19d7af0dc5850bbb2fb44aa10b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b72f61013ed13acae0442a107a91c51a39bcf19d7af0dc5850bbb2fb44aa10b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_empty on fresh value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has schema_version 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
