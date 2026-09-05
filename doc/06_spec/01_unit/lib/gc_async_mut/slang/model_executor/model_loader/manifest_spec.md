# Manifest Specification

> Tests covering TensorPackManifest.empty, parse_manifest, build_tensor_pack, serialize_manifest (A2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
step("has schema_version 0")
val m = TensorPackManifest.empty()
expect(m.schema_version).to_equal(0)
```

</details>

### parse_manifest

#### rejects empty input

- rejects empty input
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty input")
val r = parse_manifest("")
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Ok on a well-formed canonical v0 manifest

- returns Ok on a well-formed canonical v0 manifest
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok on a well-formed canonical v0 manifest")
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val r = parse_manifest(sdn)
expect(r.is_ok()).to_equal(true)
```

</details>

#### keeps parsed model metadata and counts

- keeps parsed model metadata and counts
   - Expected: m.model_id equals `demo`
   - Expected: m.revision equals `v0`
   - Expected: m.preferred_chunk_bytes equals `2097152`
   - Expected: m.chunk_count equals `0`
   - Expected: m.tensor_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps parsed model metadata and counts")
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val r = parse_manifest(sdn)
match r:
    Ok(m) =>
        expect(m.model_id).to_equal("demo")
        expect(m.revision).to_equal("v0")
        expect(m.preferred_chunk_bytes).to_equal(2097152)
        expect(m.chunk_count).to_equal(0)
        expect(m.tensor_count).to_equal(0)
    Err(_) =>
        fail("canonical manifest should parse")
```

</details>

### build_tensor_pack

#### materialises a pack from a parsed manifest

- materialises a pack from a parsed manifest
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("materialises a pack from a parsed manifest")
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val m = parse_manifest(sdn).unwrap()
val r = build_tensor_pack("/tmp/pack", m)
expect(r.is_ok()).to_equal(true)
```

</details>

#### copies parsed manifest fields into the pack

- copies parsed manifest fields into the pack
   - Expected: pack.pack_root equals `/tmp/pack`
   - Expected: pack.model_id equals `demo`
   - Expected: pack.revision equals `v0`
   - Expected: pack.preferred_chunk_bytes equals `2097152`
   - Expected: pack.chunk_count() equals `0`
   - Expected: pack.tensor_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("copies parsed manifest fields into the pack")
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val m = parse_manifest(sdn).unwrap()
val r = build_tensor_pack("/tmp/pack", m)
match r:
    Ok(pack) =>
        expect(pack.pack_root).to_equal("/tmp/pack")
        expect(pack.model_id).to_equal("demo")
        expect(pack.revision).to_equal("v0")
        expect(pack.preferred_chunk_bytes).to_equal(2097152)
        expect(pack.chunk_count()).to_equal(0)
        expect(pack.tensor_count()).to_equal(0)
    Err(_) =>
        fail("canonical manifest should materialise")
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
| Source | `test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TensorPackManifest.empty, parse_manifest, build_tensor_pack, serialize_manifest (A2).
- TensorPackManifest.empty
- parse_manifest
- build_tensor_pack
- serialize_manifest (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0237e25ceb50773da5a4135ca79f3dde3d7e5707404c93b9241ecd72741eb25f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0237e25ceb50773da5a4135ca79f3dde3d7e5707404c93b9241ecd72741eb25f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0237e25ceb50773da5a4135ca79f3dde3d7e5707404c93b9241ecd72741eb25f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_empty on fresh value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has schema_version 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/manifest_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
