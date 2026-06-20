# Transport Specification

> <details>

<!-- sdn-diagram:id=transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transport Specification

## Scenarios

### MemNvfsClient

### mem_nvfs_image + has

#### has() is true for the manifest path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
expect(client.has("/root/manifest.sdn")).to_equal(true)
```

</details>

#### has() is true for each chunk path

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
var j = 0
while j < pack.chunks.len():
    expect(client.has("/root/" + pack.chunks[j].relative_path)).to_equal(true)
    j = j + 1
```

</details>

#### has() is false for an absent path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
expect(client.has("/root/nonexistent.bin")).to_equal(false)
```

</details>

### read_text

#### returns Ok for the manifest path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val r = client.read_text("/root/manifest.sdn")
expect(_mem_text_err_code(r) == 0).to_equal(true)
```

</details>

#### returned manifest text equals the stored text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val r = client.read_text("/root/manifest.sdn")
val got = r.unwrap()
expect((got == mtext)).to_equal(true)
```

</details>

#### returns NotFound for an absent path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = mem_nvfs_image("/root", "manifest", [], [])
val r = client.read_text("/root/missing.sdn")
expect((_mem_text_err_code(r) == 1)).to_equal(true)
```

</details>

#### returns NotFound when reading a byte object as text (is_text guard)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
# A chunk object has is_text=false; reading it via read_text must fail
val chunk_path = "/root/" + pack.chunks[0].relative_path
val r = client.read_text(chunk_path)
expect((_mem_text_err_code(r) == 1)).to_equal(true)
```

</details>

### read_bytes

#### returns Ok for a chunk path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val r = client.read_bytes("/root/" + pack.chunks[0].relative_path)
expect((_mem_bytes_err_code(r) == 0)).to_equal(true)
```

</details>

#### returned buffer length equals chunk byte_len

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val r = client.read_bytes("/root/" + pack.chunks[0].relative_path)
val buf = r.unwrap()
expect((buf.len() == pack.chunks[0].byte_len)).to_equal(true)
```

</details>

#### returns NotFound for an absent path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = mem_nvfs_image("/root", "manifest", [], [])
val r = client.read_bytes("/root/data-000.bin")
expect((_mem_bytes_err_code(r) == 1)).to_equal(true)
```

</details>

#### returns NotFound when reading the manifest path as bytes (is_text guard)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
# The manifest object has is_text=true; reading it via read_bytes must fail
val r = client.read_bytes("/root/manifest.sdn")
expect((_mem_bytes_err_code(r) == 1)).to_equal(true)
```

</details>

### type-aware lookup (P3a collision fix)

#### read_bytes finds byte object even when text object is stored first at same path

- objs push
- objs push
   - Expected: (_mem_bytes_err_code(r) == 0) is true
   - Expected: (buf.len() == 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var objs: [MemObj] = []
objs.push(MemObj(path: "/root/dup", is_text: true,  text_val: "hello", bytes_val: []))
objs.push(MemObj(path: "/root/dup", is_text: false, text_val: "",      bytes_val: [0xAB as u8, 0xCD as u8]))
val client = MemNvfsClient(objs: objs)
val r = client.read_bytes("/root/dup")
# Must be Ok (err_code 0), not NotFound (err_code 1)
expect((_mem_bytes_err_code(r) == 0)).to_equal(true)
# Byte content must match what was stored
val buf = r.unwrap()
expect((buf.len() == 2)).to_equal(true)
```

</details>

#### read_text finds text object even when byte object is stored first at same path

- objs2 push
- objs2 push
   - Expected: (_mem_text_err_code(r2) == 0) is true
   - Expected: (got == "world") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var objs2: [MemObj] = []
objs2.push(MemObj(path: "/root/p2", is_text: false, text_val: "",      bytes_val: [0x01 as u8]))
objs2.push(MemObj(path: "/root/p2", is_text: true,  text_val: "world", bytes_val: []))
val client2 = MemNvfsClient(objs: objs2)
val r2 = client2.read_text("/root/p2")
# Must be Ok (err_code 0), not NotFound (err_code 1)
expect((_mem_text_err_code(r2) == 0)).to_equal(true)
val got = r2.unwrap()
expect((got == "world")).to_equal(true)
```

</details>

#### has() returns true for a path that has only a text object

- objs3 push
   - Expected: client3.has("/root/only_text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var objs3: [MemObj] = []
objs3.push(MemObj(path: "/root/only_text", is_text: true, text_val: "x", bytes_val: []))
val client3 = MemNvfsClient(objs: objs3)
expect(client3.has("/root/only_text")).to_equal(true)
```

</details>

#### has() returns true for a path that has only a byte object

- objs4 push
   - Expected: client4.has("/root/only_bytes") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var objs4: [MemObj] = []
objs4.push(MemObj(path: "/root/only_bytes", is_text: false, text_val: "", bytes_val: [0x01 as u8]))
val client4 = MemNvfsClient(objs: objs4)
expect(client4.has("/root/only_bytes")).to_equal(true)
```

</details>

### load_model_from_pack_via

### happy path

#### result is Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val result = load_model_from_pack_via(client, "/root", 0)
expect(result.is_ok()).to_equal(true)
```

</details>

#### staged_tensor_count equals pack.tensors.len()

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val result = load_model_from_pack_via(client, "/root", 0)
val lr = result.unwrap()
expect((lr.staged_tensor_count == pack.tensors.len())).to_equal(true)
```

</details>

#### bytes_streamed equals sum of chunk byte_lens

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val result = load_model_from_pack_via(client, "/root", 0)
val lr = result.unwrap()
val expected_bytes = _sum_chunk_byte_lens(pack)
expect((lr.bytes_streamed == expected_bytes)).to_equal(true)
```

</details>

#### op_count equals plan_stream(pack, granule).op_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val granule: i64 = 0
val result = load_model_from_pack_via(client, "/root", granule)
val lr = result.unwrap()
val expected_ops = plan_stream(pack, granule).op_count
expect((lr.op_count == expected_ops)).to_equal(true)
```

</details>

#### lr.pack.tensors.len() equals pack.tensors.len()

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
val result = load_model_from_pack_via(client, "/root", 0)
val lr = result.unwrap()
expect((lr.pack.tensors.len() == pack.tensors.len())).to_equal(true)
```

</details>

### error paths

#### wrong pack_root -> PackRootNotFound (err_code 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), _make_chunk_buffers(pack))
# Use a different root so the manifest object is not found
val result = load_model_from_pack_via(client, "/wrong_root", 0)
expect(result.is_err()).to_equal(true)
expect((_loader_err_code(result) == 0)).to_equal(true)
```

</details>

#### valid manifest but no chunk objects -> ChunkOpenFailed (err_code 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
# Store only the manifest text; no chunk byte objects
val client = mem_nvfs_image("/root", mtext, [], [])
val result = load_model_from_pack_via(client, "/root", 0)
expect(result.is_err()).to_equal(true)
expect((_loader_err_code(result) == 2)).to_equal(true)
```

</details>

#### garbage manifest_text -> ManifestInvalid (err_code 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = mem_nvfs_image("/root", "this is not valid manifest content", [], [])
val result = load_model_from_pack_via(client, "/root", 0)
expect(result.is_err()).to_equal(true)
expect((_loader_err_code(result) == 1)).to_equal(true)
```

</details>

#### chunk object exists but has empty buffer -> ChunkOpenFailed (err_code 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_test_pack()
val mtext = _make_manifest_text(pack)
# Pass chunk_paths so the chunk object IS created, but chunk_bytes=[]
# so its buffer is stored as empty ([]).
val client = mem_nvfs_image("/root", mtext, _chunk_paths(pack), [])
val result = load_model_from_pack_via(client, "/root", 0)
expect(result.is_err()).to_equal(true)
expect((_loader_err_code(result) == 2)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MemNvfsClient
- mem_nvfs_image + has
- read_text
- read_bytes
- type-aware lookup (P3a collision fix)
- load_model_from_pack_via
- happy path
- error paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
