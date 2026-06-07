# Tls12 Prf Kat Specification

> <details>

<!-- sdn-diagram:id=tls12_prf_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls12_prf_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls12_prf_kat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls12_prf_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls12 Prf Kat Specification

## Scenarios

### TLS 1.2 P_SHA-256 — IETF reference vector

#### P_SHA256(secret, 'test label'||seed, 100) matches the IETF reference output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The full 100-byte expected OKM.
# This forces 4 iterations of the HMAC A-chain (4*32=128, truncated to 100)
# so both "multi-iteration" and "truncation" edges are exercised.
expect(bytes_to_hex(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 100))).to_equal(
    "e3f229ba727be17b8d122620557cd453c2aab21d07c3d495329b52d4e61edb5a6b301791e90d35c9c9a46b4e14baf9af0fa022f7077def17abfd3797c0564bab4fbc91666e9def9b97fce34f796789baa48082d122ee42c5a72e5a5110fff70187347b66"
)
```

</details>

#### tls12_prf_sha256 wrapper composes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tls12_prf_sha256(secret, "test label", seed, 100) == p_hash_sha256(secret, "test label"||seed, 100)
expect(bytes_to_hex(tls12_prf_sha256(_ietf_secret(), "test label", _ietf_seed(), 100))).to_equal(
    "e3f229ba727be17b8d122620557cd453c2aab21d07c3d495329b52d4e61edb5a6b301791e90d35c9c9a46b4e14baf9af0fa022f7077def17abfd3797c0564bab4fbc91666e9def9b97fce34f796789baa48082d122ee42c5a72e5a5110fff70187347b66"
)
```

</details>

#### tls12_prf(use_sha384=false) equals tls12_prf_sha256

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = bytes_to_hex(tls12_prf(_ietf_secret(), "test label", _ietf_seed(), 64, false))
val b = bytes_to_hex(tls12_prf_sha256(_ietf_secret(), "test label", _ietf_seed(), 64))
expect(a).to_equal(b)
```

</details>

### TLS 1.2 P_hash boundary behavior

#### P_SHA256 with output_len=12 (truncation < HashLen=32) returns 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 12 is the verify_data length used by Finished — common truncation case.
expect(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 12).len()).to_equal(12)
```

</details>

#### P_SHA256 with output_len=12 prefix matches output_len=32 prefix

1. prefix = prefix + long32 char at
   - Expected: short equals `prefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short = bytes_to_hex(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 12))
val long32 = bytes_to_hex(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 32))
# First 24 hex chars (12 bytes) of the 32-byte result must equal the 12-byte result.
var prefix = ""
var i = 0
while i < 24:
    prefix = prefix + long32.char_at(i)
    i = i + 1
expect(short).to_equal(prefix)
```

</details>

#### P_SHA256 with output_len=64 prefix matches output_len=32 prefix

1. prefix = prefix + len64 char at
   - Expected: prefix equals `len32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# output_len=64 = 2 HMAC blocks; first 32 must equal output_len=32 single block.
val len32 = bytes_to_hex(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 32))
val len64 = bytes_to_hex(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 64))
var prefix = ""
var i = 0
while i < 64:
    prefix = prefix + len64.char_at(i)
    i = i + 1
expect(prefix).to_equal(len32)
```

</details>

#### P_SHA256 with output_len=0 returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(p_hash_sha256(_ietf_secret(), _ietf_label_seed(), 0).len()).to_equal(0)
```

</details>

#### P_SHA384 with output_len=96 (= 2 * HashLen=48) produces 96 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SHA-384 HashLen=48; output_len=96 forces 2 A-chain iterations exactly.
expect(p_hash_sha384(_ietf_secret(), _ietf_label_seed(), 96).len()).to_equal(96)
```

</details>

#### P_SHA384 with output_len=24 (truncation < HashLen=48) returns 24 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(p_hash_sha384(_ietf_secret(), _ietf_label_seed(), 24).len()).to_equal(24)
```

</details>

### TLS 1.2 master_secret (RFC 5246 §8.1)

#### master_secret is exactly 48 bytes for SHA-256 PRF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
expect(ms.len()).to_equal(48)
```

</details>

#### master_secret is exactly 48 bytes for SHA-384 PRF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), true)
expect(ms.len()).to_equal(48)
```

</details>

#### master_secret is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = bytes_to_hex(tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false))
val b = bytes_to_hex(tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false))
expect(a).to_equal(b)
```

</details>

#### master_secret SHA-384 differs from SHA-256 for same inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sha256 = bytes_to_hex(tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false))
val sha384 = bytes_to_hex(tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), true))
# Two independent PRFs must produce different outputs with overwhelming probability.
expect(sha256 == sha384).to_equal(false)
```

</details>

#### master_secret swapping client/server randoms changes output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "master secret" PRF concatenates client_random || server_random, so
# swapping the two operands must change the result.
val a = bytes_to_hex(tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false))
val b = bytes_to_hex(tls12_master_secret(_ietf_secret(), _ones32(), _zeros32(), false))
expect(a == b).to_equal(false)
```

</details>

### TLS 1.2 key_block (RFC 5246 §6.3)

#### key_block returns the requested length (104 bytes — typical AES-128-SHA256 sizing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2 * (mac_key=32 + enc_key=16 + iv=4) = 104 for AES_128_GCM_SHA256.
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
val kb = tls12_key_block(ms, _ones32(), _zeros32(), 104, false)
expect(kb.len()).to_equal(104)
```

</details>

#### key_block uses server_random || client_random ordering (different from master_secret)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# master_secret uses (client_random, server_random); key_block uses
# (server_random, client_random). Swap operands and verify they differ.
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
val kb1 = bytes_to_hex(tls12_key_block(ms, _ones32(), _zeros32(), 64, false))
val kb2 = bytes_to_hex(tls12_key_block(ms, _zeros32(), _ones32(), 64, false))
expect(kb1 == kb2).to_equal(false)
```

</details>

### TLS 1.2 Finished verify_data (RFC 5246 §7.4.9)

#### client_finished verify_data is exactly 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
# transcript_hash is the 32-byte SHA-256 digest of the handshake record;
# we fake it here with an attested 32-byte input.
val vd = tls12_finished_verify_data(ms, _ietf_label_seed(), true, false)
expect(vd.len()).to_equal(12)
```

</details>

#### server_finished verify_data is exactly 12 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
val vd = tls12_finished_verify_data(ms, _ietf_label_seed(), false, false)
expect(vd.len()).to_equal(12)
```

</details>

#### client_finished and server_finished produce different verify_data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The labels "client finished" vs "server finished" must yield distinct
# output for the same master_secret + transcript_hash.
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
val client_vd = bytes_to_hex(tls12_finished_verify_data(ms, _ietf_label_seed(), true, false))
val server_vd = bytes_to_hex(tls12_finished_verify_data(ms, _ietf_label_seed(), false, false))
expect(client_vd == server_vd).to_equal(false)
```

</details>

#### verify_data is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
val a = bytes_to_hex(tls12_finished_verify_data(ms, _ietf_label_seed(), true, false))
val b = bytes_to_hex(tls12_finished_verify_data(ms, _ietf_label_seed(), true, false))
expect(a).to_equal(b)
```

</details>

#### SHA-384 PRF Finished differs from SHA-256 PRF Finished

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms256 = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), false)
val ms384 = tls12_master_secret(_ietf_secret(), _zeros32(), _ones32(), true)
val vd256 = bytes_to_hex(tls12_finished_verify_data(ms256, _ietf_label_seed(), true, false))
val vd384 = bytes_to_hex(tls12_finished_verify_data(ms384, _ietf_label_seed(), true, true))
expect(vd256 == vd384).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/tls12_prf_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS 1.2 P_SHA-256 — IETF reference vector
- TLS 1.2 P_hash boundary behavior
- TLS 1.2 master_secret (RFC 5246 §8.1)
- TLS 1.2 key_block (RFC 5246 §6.3)
- TLS 1.2 Finished verify_data (RFC 5246 §7.4.9)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
