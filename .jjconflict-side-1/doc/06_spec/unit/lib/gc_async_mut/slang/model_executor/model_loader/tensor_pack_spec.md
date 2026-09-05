# Tensor Pack Specification

> Tests covering TensorPack.empty, TensorPack.find_tensor, ChunkInfo, DEFAULT constants (A2), plan_chunks (A2), write_chunk (A2), sha256_chunk (A2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Pack Specification

## Scenarios

### TensorPack.empty

#### has the supplied pack_root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has the supplied pack_root
   - Expected: pack.pack_root equals `/models/llama3-8b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has the supplied pack_root")
val pack = TensorPack.empty("/models/llama3-8b")
expect(pack.pack_root).to_equal("/models/llama3-8b")
```

</details>

#### has zero tensors and chunks

- has zero tensors and chunks
   - Expected: pack.tensor_count() equals `0`
   - Expected: pack.chunk_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has zero tensors and chunks")
val pack = TensorPack.empty("/x")
expect(pack.tensor_count()).to_equal(0)
expect(pack.chunk_count()).to_equal(0)
```

</details>

#### has empty model_id and revision

- has empty model_id and revision
   - Expected: pack.model_id equals ``
   - Expected: pack.revision equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has empty model_id and revision")
val pack = TensorPack.empty("/x")
expect(pack.model_id).to_equal("")
expect(pack.revision).to_equal("")
```

</details>

### TensorPack.find_tensor

#### returns empty-named TensorInfo when missing

- returns empty-named TensorInfo when missing
   - Expected: t.name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty-named TensorInfo when missing")
val pack = TensorPack.empty("/x")
val t = pack.find_tensor("missing")
expect(t.name).to_equal("")
```

</details>

#### finds a tensor that is present

- finds a tensor that is present
   - Expected: t.name equals `w0`
   - Expected: t.byte_len equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a tensor that is present")
var pack = TensorPack.empty("/x")
val shape: [i64] = [4, 8]
pack.tensors.push(TensorInfo(
    name: "w0",
    shape: shape,
    dtype: Dtype.F16,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 64
))
val t = pack.find_tensor("w0")
expect(t.name).to_equal("w0")
expect(t.byte_len).to_equal(64)
```

</details>

### ChunkInfo

#### stores relative path and digest

- stores relative path and digest
   - Expected: c.relative_path equals `data-000.bin`
   - Expected: c.digest_hex equals `0011aabb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores relative path and digest")
val c = ChunkInfo(
    id: 0,
    relative_path: "data-000.bin",
    byte_len: 2097152,
    digest_hex: "0011aabb"
)
expect(c.relative_path).to_equal("data-000.bin")
expect(c.digest_hex).to_equal("0011aabb")
```

</details>

### DEFAULT constants (A2)

#### chunk align is 4 KiB

- chunk align is 4 KiB
   - Expected: DEFAULT_CHUNK_ALIGN equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chunk align is 4 KiB")
expect(DEFAULT_CHUNK_ALIGN).to_equal(4096)
```

</details>

#### preferred chunk bytes is 2 MiB

- preferred chunk bytes is 2 MiB
   - Expected: DEFAULT_PREFERRED_CHUNK_BYTES equals `2097152`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preferred chunk bytes is 2 MiB")
expect(DEFAULT_PREFERRED_CHUNK_BYTES).to_equal(2097152)
```

</details>

### plan_chunks (A2)

#### emits a single chunk for two small tensors (16B + 24B, fits in one 2 MiB chunk)

- emits a single chunk for two small tensors (16B + 24B, fits in one 2 MiB chunk)
   - Expected: pack.chunk_count() equals `1`
   - Expected: pack.tensor_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a single chunk for two small tensors (16B + 24B, fits in one 2 MiB chunk)")
val tensors = [
    TensorInfo(name: "w", shape: [2, 2], dtype: Dtype.F32,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 16),
    TensorInfo(name: "b", shape: [3], dtype: Dtype.I64,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 24)
]
val pack = plan_chunks(tensors, DEFAULT_CHUNK_ALIGN, DEFAULT_PREFERRED_CHUNK_BYTES)
expect(pack.chunk_count()).to_equal(1)
expect(pack.tensor_count()).to_equal(2)
```

</details>

#### aligns the second tensor to DEFAULT_CHUNK_ALIGN (4096)

- aligns the second tensor to DEFAULT_CHUNK_ALIGN (4096)
   - Expected: second.offset_in_chunk equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aligns the second tensor to DEFAULT_CHUNK_ALIGN (4096)")
val tensors = [
    TensorInfo(name: "w", shape: [2, 2], dtype: Dtype.F32,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 16),
    TensorInfo(name: "b", shape: [3], dtype: Dtype.I64,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 24)
]
val pack = plan_chunks(tensors, DEFAULT_CHUNK_ALIGN, DEFAULT_PREFERRED_CHUNK_BYTES)
val second = pack.tensors[1]
# 16 bytes then align-up to 4096.
expect(second.offset_in_chunk).to_equal(4096)
```

</details>

### write_chunk (A2)

#### emits chunk bytes of expected length (tensor bytes + align padding)

- emits chunk bytes of expected length (tensor bytes + align padding)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits chunk bytes of expected length (tensor bytes + align padding)")
val t = TensorInfo(name: "w", shape: [2, 2], dtype: Dtype.F32,
                   chunk_id: 0, offset_in_chunk: 0, byte_len: 16)
var src: [u8] = []
var i = 0
while i < 16:
    src.push(0xAB as u8)
    i = i + 1
val out = write_chunk(t, src, DEFAULT_CHUNK_ALIGN)
# First 16 bytes are the tensor; remainder (if any) is zero padding.
expect(out.len()).to_be_greater_than(15)
```

</details>

### sha256_chunk (A2)

#### returns a 64-char lowercase hex digest

- returns a 64-char lowercase hex digest
   - Expected: hex.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a 64-char lowercase hex digest")
var bytes: [u8] = []
var i = 0
while i < 16:
    bytes.push(0 as u8)
    i = i + 1
val hex = sha256_chunk(bytes)
expect(hex.len()).to_equal(64)
```

</details>

#### is deterministic (same input => same hex)

- is deterministic (same input => same hex)
   - Expected: sha256_chunk(a) equals `sha256_chunk(b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is deterministic (same input => same hex)")
var a: [u8] = []
var b: [u8] = []
var i = 0
while i < 8:
    a.push(0x42 as u8)
    b.push(0x42 as u8)
    i = i + 1
expect(sha256_chunk(a)).to_equal(sha256_chunk(b))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TensorPack.empty, TensorPack.find_tensor, ChunkInfo, DEFAULT constants (A2), plan_chunks (A2), write_chunk (A2), sha256_chunk (A2).
- TensorPack.empty
- TensorPack.find_tensor
- ChunkInfo
- DEFAULT constants (A2)
- plan_chunks (A2)
- write_chunk (A2)
- sha256_chunk (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `c6b710f77766c908f13e92899160ec0cddace75f62c97ca47c748c370b66e64d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6b710f77766c908f13e92899160ec0cddace75f62c97ca47c748c370b66e64d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6b710f77766c908f13e92899160ec0cddace75f62c97ca47c748c370b66e64d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has the supplied pack_root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has zero tensors and chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_executor/model_loader/tensor_pack_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has empty model_id and revision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
