# Streamer Specification

> <details>

<!-- sdn-diagram:id=streamer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=streamer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

streamer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=streamer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Streamer Specification

## Scenarios

### plan_stream empty pack

#### produces zero ops, zero total_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = TensorPack.empty("/x")
val plan = plan_stream(empty, 4)
expect(plan.op_count).to_equal(0)
expect(plan.total_bytes).to_equal(0)
```

</details>

#### op list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = TensorPack.empty("/x")
val plan = plan_stream(empty, 4)
expect(plan.ops.len()).to_equal(0)
```

</details>

### plan_stream zero-byte chunk

#### granule<=0 emits no op for a zero-byte chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a single zero-byte TensorInfo — plan_chunks with align=1
# yields a chunk with byte_len=0.
var tinfos: [TensorInfo] = []
tinfos.push(TensorInfo(
    name: "empty_w",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 0
))
val pack = plan_chunks(tinfos, 1, 1073741824)
val plan = plan_stream(pack, 0)
expect(plan.op_count).to_equal(0)
expect(plan.total_bytes).to_equal(0)
```

</details>

#### granule>0 emits no op for a zero-byte chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tinfos: [TensorInfo] = []
tinfos.push(TensorInfo(
    name: "empty_w",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 0
))
val pack = plan_chunks(tinfos, 1, 1073741824)
val plan = plan_stream(pack, 4)
expect(plan.op_count).to_equal(0)
expect(plan.total_bytes).to_equal(0)
```

</details>

### plan_stream granule<=0

#### single chunk → single op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 12)
val plan = plan_stream(pack, 0)
expect(plan.op_count).to_equal(1)
expect(plan.total_bytes).to_equal(pack.chunks[0].byte_len)
```

</details>

#### negative granule also gives one op per chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 12)
val plan = plan_stream(pack, -1)
expect(plan.op_count).to_equal(1)
```

</details>

#### op covers full chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 16)
val plan = plan_stream(pack, 0)
val op = plan.ops[0]
expect(op.offset).to_equal(0)
expect(op.length).to_equal(pack.chunks[0].byte_len)
```

</details>

### plan_stream granule larger than chunk

#### single op with length == byte_len

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 8)
val plan = plan_stream(pack, 1024)
expect(plan.op_count).to_equal(1)
val op = plan.ops[0]
expect(op.offset).to_equal(0)
expect(op.length).to_equal(pack.chunks[0].byte_len)
expect(plan.total_bytes).to_equal(pack.chunks[0].byte_len)
```

</details>

### plan_stream exact granule division

#### 4-byte chunk, granule=2 → exactly 2 ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 4)
val plan = plan_stream(pack, 2)
expect(plan.op_count).to_equal(2)
expect(plan.total_bytes).to_equal(4)
```

</details>

#### no op has length 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 4)
val plan = plan_stream(pack, 2)
var i = 0
var any_zero = false
while i < plan.ops.len():
    if plan.ops[i].length == 0:
        any_zero = true
    i = i + 1
expect(any_zero).to_equal(false)
```

</details>

#### 6-byte chunk, granule=2 → 3 ops, total_bytes=6

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 6)
val plan = plan_stream(pack, 2)
expect(plan.op_count).to_equal(3)
expect(plan.total_bytes).to_equal(6)
```

</details>

### plan_stream partial tail op

#### 7-byte chunk, granule=4 → 2 ops (4+3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 7)
val plan = plan_stream(pack, 4)
expect(plan.op_count).to_equal(2)
val op0 = plan.ops[0]
val op1 = plan.ops[1]
expect(op0.length).to_equal(4)
expect(op1.length).to_equal(3)
expect(plan.total_bytes).to_equal(7)
```

</details>

#### op offsets are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 7)
val plan = plan_stream(pack, 4)
expect(plan.ops[0].offset).to_equal(0)
expect(plan.ops[1].offset).to_equal(4)
```

</details>

### plan_stream total_bytes invariant

#### total_bytes == chunk.byte_len for single chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 9)
val plan = plan_stream(pack, 3)
expect(plan.total_bytes).to_equal(pack.chunks[0].byte_len)
```

</details>

#### sum of op lengths == total_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 9)
val plan = plan_stream(pack, 4)
var sum: i64 = 0
var i = 0
while i < plan.ops.len():
    sum = sum + plan.ops[i].length
    i = i + 1
expect(sum).to_equal(plan.total_bytes)
```

</details>

#### plan_stream.total_bytes == stream_pack.bytes_streamed for 2-tensor split pack

- tinfos push
- tinfos push
- chunk data push
- Ok
   - Expected: plan.total_bytes equals `res.bytes_streamed`
   - Expected: res.stages.len() equals `2`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two tensors of 5 bytes each → two chunks of 5 bytes (align=1,
# preferred_chunk_bytes=5 so each tensor gets its own chunk).
var tinfos: [TensorInfo] = []
tinfos.push(TensorInfo(name: "a", shape: [5], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 5))
tinfos.push(TensorInfo(name: "b", shape: [5], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 5))
val pack = plan_chunks(tinfos, 1, 5)
# Granule=3 splits at least the first 5-byte chunk into 2 ops (3+2)
val plan = plan_stream(pack, 3)
# Build chunk_data matching each chunk's byte_len
var chunk_data: [[u8]] = []
var ci = 0
while ci < pack.chunks.len():
    chunk_data.push(_fill_buf(pack.chunks[ci].byte_len, ci + 1))
    ci = ci + 1
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(plan.total_bytes).to_equal(res.bytes_streamed)
        expect(res.stages.len()).to_equal(2)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### stream_pack gather correctness

#### staged bytes match chunk slice at index 0

- Ok
   - Expected: b0 equals `42`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 8)
val chunk_data = _make_chunk_data(pack, [42])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        val stage = res.stages[0]
        val b0 = (stage.bytes[0] as i64) & 0xFF
        expect(b0).to_equal(42)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### staged bytes match chunk slice at last index

- Ok
   - Expected: bLast equals `99`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 8)
val chunk_data = _make_chunk_data(pack, [99])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        val stage = res.stages[0]
        val last_idx = stage.bytes.len() - 1
        val bLast = (stage.bytes[last_idx] as i64) & 0xFF
        expect(bLast).to_equal(99)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### staged bytes length equals tensor byte_len

- Ok
   - Expected: res.stages[0].bytes.len() equals `10`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 10)
val chunk_data = _make_chunk_data(pack, [0x42])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.stages[0].bytes.len()).to_equal(10)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### gathers exact slice: offset=2 len=3 from positional buffer [0..7]

- var pack = TensorPack empty
- chunk data push
- Ok
   - Expected: stage.bytes.len() equals `3`
   - Expected: b0 equals `2`
   - Expected: b2 equals `4`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Positional fill: buf[i]=i so buf=[0,1,2,3,4,5,6,7].
# Tensor at offset=2, byte_len=3 → should copy [2,3,4].
# A start-offset bug (e.g. [1,2,3] or [3,4,5]) fails this check.
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(
    id: 0,
    relative_path: "data-000.bin",
    byte_len: 8,
    digest_hex: ""
))
pack.tensors.push(TensorInfo(
    name: "slice_w",
    shape: [3],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: 2,
    byte_len: 3
))
val buf = _fill_positional(8)
var chunk_data: [[u8]] = []
chunk_data.push(buf)
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        val stage = res.stages[0]
        expect(stage.bytes.len()).to_equal(3)
        val b0 = (stage.bytes[0] as i64) & 0xFF
        val b2 = (stage.bytes[2] as i64) & 0xFF
        # b0 must be 2 (position 0 of [2,3,4]) — NOT 1 or 3
        expect(b0).to_equal(2)
        # b2 must be 4 (position 2 of [2,3,4]) — NOT 3 or 5
        expect(b2).to_equal(4)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### stream_pack result fields

#### bytes_streamed equals sum of chunk byte_lens

- Ok
   - Expected: res.bytes_streamed equals `pack.chunks[0].byte_len`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 8)
val chunk_data = _make_chunk_data(pack, [0x01])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.bytes_streamed).to_equal(pack.chunks[0].byte_len)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### staged_bytes equals tensor byte_len

- Ok
   - Expected: res.staged_bytes equals `6`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 6)
val chunk_data = _make_chunk_data(pack, [0x02])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.staged_bytes).to_equal(6)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### stages.len() equals tensor count

- Ok
   - Expected: res.stages.len() equals `1`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 4)
val chunk_data = _make_chunk_data(pack, [0x03])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.stages.len()).to_equal(1)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### stage name matches tensor name

- Ok
   - Expected: res.stages[0].name equals `my_tensor`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("my_tensor", 4)
val chunk_data = _make_chunk_data(pack, [0x07])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.stages[0].name).to_equal("my_tensor")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### stage chunk_id matches tensor chunk_id

- Ok
   - Expected: res.stages[0].chunk_id equals `0`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 4)
val chunk_data = _make_chunk_data(pack, [0x07])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.stages[0].chunk_id).to_equal(0)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### stream_pack ChunkDataMissing

#### returns Err(ChunkDataMissing) when no buffers supplied

- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_single_tensor_pack("w0", 4)
var chunk_data: [[u8]] = []
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.ChunkDataMissing) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

#### returns Err(ChunkDataMissing) when one buffer short for 1-chunk pack

- var pack = TensorPack empty
- pack chunks push
- pack tensors push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pack has 1 chunk but we pass 0 buffers (already tested); this
# double-checks the count comparison path.
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 4, digest_hex: ""))
pack.tensors.push(TensorInfo(name: "w0", shape: [], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 4))
var chunk_data: [[u8]] = []
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.ChunkDataMissing) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

### stream_pack ChunkTooShort

#### returns Err(ChunkTooShort) when buffer shorter than chunk.byte_len

- var pack = TensorPack empty
- pack chunks push
- pack tensors push
- chunk data push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 8, digest_hex: ""))
pack.tensors.push(TensorInfo(name: "w0", shape: [], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 4))
# Buffer only 4 bytes, but chunk.byte_len is 8
val short_buf = _fill_buf(4, 0x00)
var chunk_data: [[u8]] = []
chunk_data.push(short_buf)
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.ChunkTooShort) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

#### exact-size buffer (==chunk.byte_len) is accepted

- var pack = TensorPack empty
- pack chunks push
- pack tensors push
- chunk data push
- Ok
   - Expected: res.staged_bytes equals `4`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 4, digest_hex: ""))
pack.tensors.push(TensorInfo(name: "w0", shape: [], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 4))
val exact_buf = _fill_buf(4, 0x11)
var chunk_data: [[u8]] = []
chunk_data.push(exact_buf)
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        expect(res.staged_bytes).to_equal(4)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

### stream_pack ChunkNotFound

#### returns Err(ChunkNotFound) when tensor chunk_id has no matching chunk

- var pack = TensorPack empty
- pack chunks push
- chunk data push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pack has chunk id=0 only; tensor references chunk_id=99
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 8, digest_hex: ""))
pack.tensors.push(TensorInfo(
    name: "bad",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 99,
    offset_in_chunk: 0,
    byte_len: 4
))
val buf = _fill_buf(8, 0x00)
var chunk_data: [[u8]] = []
chunk_data.push(buf)
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.ChunkNotFound) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

### stream_pack TensorOutOfBounds

#### offset + byte_len exceeds buffer → Err(TensorOutOfBounds)

- var pack = TensorPack empty
- pack chunks push
- chunk data push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# chunk.byte_len=8 so buffer passes ChunkTooShort; tensor OOB
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 8, digest_hex: ""))
pack.tensors.push(TensorInfo(
    name: "oob",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: 6,
    byte_len: 4
))
# offset(6) + byte_len(4) = 10 > buf.len(8)
val buf = _fill_buf(8, 0x00)
var chunk_data: [[u8]] = []
chunk_data.push(buf)
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.TensorOutOfBounds) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

#### negative offset → Err(TensorOutOfBounds)

- var pack = TensorPack empty
- pack chunks push
- chunk data push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 8, digest_hex: ""))
pack.tensors.push(TensorInfo(
    name: "neg",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: -1,
    byte_len: 4
))
val buf = _fill_buf(8, 0x00)
var chunk_data: [[u8]] = []
chunk_data.push(buf)
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.TensorOutOfBounds) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

#### negative byte_len → Err(TensorOutOfBounds)

- var pack = TensorPack empty
- pack chunks push
- chunk data push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 8, digest_hex: ""))
pack.tensors.push(TensorInfo(
    name: "neg_len",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: -1
))
val buf = _fill_buf(8, 0x00)
var chunk_data: [[u8]] = []
chunk_data.push(buf)
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.TensorOutOfBounds) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

#### OOB tensor rejected even when buf padded beyond chunk.byte_len (P3b tightened bound)

- var pack = TensorPack empty
- pack chunks push
- chunk data push
- Err
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# chunk.byte_len=8; tensor offset=6, byte_len=4 → end=10 > chunk.byte_len=8.
# Buffer is padded to 16 bytes so it would have passed the old buf.len() check.
# The tightened bound (end > chunk.byte_len) still catches this.
var pack = TensorPack.empty("/x")
pack.chunks.push(ChunkInfo(id: 0, relative_path: "data-000.bin", byte_len: 8, digest_hex: ""))
pack.tensors.push(TensorInfo(
    name: "padded_oob",
    shape: [],
    dtype: Dtype.U8,
    chunk_id: 0,
    offset_in_chunk: 6,
    byte_len: 4
))
# offset(6) + byte_len(4) = 10 > chunk.byte_len(8), but buf.len()=16 would pass old guard
val buf = _fill_buf(16, 0xCC)
var chunk_data: [[u8]] = []
chunk_data.push(buf)
val r = stream_pack(pack, chunk_data)
match r:
    Err(StreamError.TensorOutOfBounds) =>
        expect(true).to_equal(true)
    _ =>
        expect(false).to_equal(true)
```

</details>

### stream_pack multi-chunk value discrimination

#### tensor in chunk 0 carries chunk-0 fill value (0xA1)

- tinfos push
- tinfos push
   - Expected: two_chunks is true
- Ok
   - Expected: v0 equals `0xA1`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two tensors of 32 bytes each. preferred_chunk_bytes=32 so plan_chunks
# places each in its own chunk. chunk 0 filled with 0xA1, chunk 1 with 0xB2.
var tinfos: [TensorInfo] = []
tinfos.push(TensorInfo(name: "t0", shape: [32], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 32))
tinfos.push(TensorInfo(name: "t1", shape: [32], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 32))
val pack = plan_chunks(tinfos, 1, 32)
# Verify the plan actually produced two separate chunks
val two_chunks = pack.chunks.len() == 2
expect(two_chunks).to_equal(true)
# Build chunk_data: chunk[0]=0xA1, chunk[1]=0xB2
val chunk_data = _make_chunk_data(pack, [0xA1, 0xB2])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        # Find the stage for t0 (chunk_id must equal chunk 0's id)
        val s0 = res.stages[0]
        val v0 = (s0.bytes[0] as i64) & 0xFF
        expect(v0).to_equal(0xA1)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### tensor in chunk 1 carries chunk-1 fill value (0xB2)

- tinfos push
- tinfos push
- Ok
   - Expected: v1 equals `0xB2`
- Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tinfos: [TensorInfo] = []
tinfos.push(TensorInfo(name: "t0", shape: [32], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 32))
tinfos.push(TensorInfo(name: "t1", shape: [32], dtype: Dtype.U8, chunk_id: 0, offset_in_chunk: 0, byte_len: 32))
val pack = plan_chunks(tinfos, 1, 32)
val chunk_data = _make_chunk_data(pack, [0xA1, 0xB2])
val r = stream_pack(pack, chunk_data)
match r:
    Ok(res) =>
        val s1 = res.stages[1]
        val v1 = (s1.bytes[0] as i64) & 0xFF
        expect(v1).to_equal(0xB2)
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/streamer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- plan_stream empty pack
- plan_stream zero-byte chunk
- plan_stream granule<=0
- plan_stream granule larger than chunk
- plan_stream exact granule division
- plan_stream partial tail op
- plan_stream total_bytes invariant
- stream_pack gather correctness
- stream_pack result fields
- stream_pack ChunkDataMissing
- stream_pack ChunkTooShort
- stream_pack ChunkNotFound
- stream_pack TensorOutOfBounds
- stream_pack multi-chunk value discrimination

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
