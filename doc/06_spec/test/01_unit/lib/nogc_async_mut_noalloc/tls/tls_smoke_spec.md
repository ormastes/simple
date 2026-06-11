# Tls Smoke Specification

> <details>

<!-- sdn-diagram:id=tls_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls_smoke_spec -> std
tls_smoke_spec -> src
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Smoke Specification

## Scenarios

### tls no-alloc smoke

#### types: content_type_from_byte round-trips 0x14

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = content_type_from_byte(0x14u8)
expect(content_type_to_byte(ct)).to_equal(0x14u8)
```

</details>

#### transcript: new transcript has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = transcript_new()
expect(tr.buf_len).to_equal(0u64)
```

</details>

#### transcript: add bytes increases buf_len

1. var tr = transcript new
2. tr = transcript add
   - Expected: tr.buf_len equals `3u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = transcript_new()
val data: [u8] = [0x01u8, 0x02u8, 0x03u8]
tr = transcript_add(tr, data)
expect(tr.buf_len).to_equal(3u64)
```

</details>

#### transcript: hash of empty transcript is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = transcript_new()
val h = transcript_hash(tr)
expect(h.len()).to_equal(32)
```

</details>

#### record: make_nonce returns 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iv: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
val nonce = record_make_nonce(iv, 0u64)
expect(nonce.len()).to_equal(12)
```

</details>

#### record: make_nonce XORs seq_num into last 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iv: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
val nonce = record_make_nonce(iv, 1u64)
expect(nonce[11]).to_equal(1u8)
```

</details>

#### handshake: parse_handshake_header of short buffer returns msg_type 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x01u8, 0x00u8, 0x00u8]
val ph = parse_handshake_header(data)
expect(ph.msg_type).to_equal(0u8)
```

</details>

#### handshake: build_finished wraps verify_data correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd: [u8] = [0xAAu8, 0xBBu8, 0xCCu8]
val msg = build_finished(vd)
# type byte is 20 (0x14) for Finished
expect(msg[0]).to_equal(20u8)
# length bytes: 0x00 0x00 0x03
expect(msg[1]).to_equal(0u8)
expect(msg[2]).to_equal(0u8)
expect(msg[3]).to_equal(3u8)
expect(msg.len()).to_equal(7)
```

</details>

#### x25519: pubkey of all-zero scalar returns 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
val pub = x25519_pubkey(scalar)
expect(pub.len()).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/tls/tls_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tls no-alloc smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
