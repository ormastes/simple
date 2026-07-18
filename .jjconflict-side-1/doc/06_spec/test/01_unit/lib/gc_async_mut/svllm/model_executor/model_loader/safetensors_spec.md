# Safetensors Specification

> <details>

<!-- sdn-diagram:id=safetensors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=safetensors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

safetensors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=safetensors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safetensors Specification

## Scenarios

### parse_safetensors_header — happy path (A2)

#### returns Ok for the tiny 2-tensor fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = build_tiny_safetensors()
val r = parse_safetensors_header(buf)
expect(r.is_ok()).to_equal(true)
```

</details>

#### records the 8-byte header length prefix value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = build_tiny_safetensors()
val r = parse_safetensors_header(buf)
val h = r.unwrap()
expect(h.header_byte_len).to_be_greater_than(100)
```

</details>

#### extracts exactly two tensor entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
expect(h.tensors.len()).to_equal(2)
```

</details>

#### first tensor is named 'w' with dtype F32

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
val w = h.tensors[0]
expect(w.name).to_equal("w")
expect(w.dtype).to_equal("F32")
expect(w.dtype_tag).to_equal(Dtype.F32)
```

</details>

#### first tensor has shape [2,2] and data_offsets [0,16]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
val w = h.tensors[0]
expect(w.shape.len()).to_equal(2)
expect(w.shape[0]).to_equal(2)
expect(w.shape[1]).to_equal(2)
expect(w.offset).to_equal(0)
expect(w.length).to_equal(16)
```

</details>

#### second tensor is named 'b' with dtype I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
val b = h.tensors[1]
expect(b.name).to_equal("b")
expect(b.dtype).to_equal("I64")
expect(b.dtype_tag).to_equal(Dtype.I64)
```

</details>

### parse_safetensors_header — error paths

#### rejects buffers shorter than 8 bytes as TruncatedHeader

- buf push
- buf push
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
buf.push(0 as u8)
buf.push(0 as u8)
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects a length prefix that overruns the buffer

- buf = push u64 le
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Prefix claims 999 bytes of JSON but buffer is only 8 bytes long.
var buf: [u8] = []
buf = push_u64_le(buf, 999)
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects malformed JSON header as MalformedJson

- buf = push u64 le
- buf = push ascii
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "not-a-json-object"
var buf: [u8] = []
buf = push_u64_le(buf, bad.len() as i64)
buf = push_ascii(buf, bad)
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects unknown dtype strings

- buf = push u64 le
- buf = push ascii
- buf push
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val j = "{\"x\":{\"dtype\":\"WEIRD\",\"shape\":[1],\"data_offsets\":[0,4]}}"
var buf: [u8] = []
buf = push_u64_le(buf, j.len() as i64)
buf = push_ascii(buf, j)
# Pad 4 bytes payload.
var i = 0
while i < 4:
    buf.push(0 as u8)
    i = i + 1
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/safetensors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_safetensors_header — happy path (A2)
- parse_safetensors_header — error paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
