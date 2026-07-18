# Finished Probe Specification

> 1. ts push

<!-- sdn-diagram:id=_finished_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_finished_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_finished_probe_spec -> std
_finished_probe_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_finished_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Finished Probe Specification

## Scenarios

### tls13_finished_key reaches interpreter

#### 32-byte HKDF-derived key from a known traffic secret

1. ts push
   - Expected: k.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    ts.push(0x42u8)
    i = i + 1u64
val k = tls13_finished_key(ts)
expect(k.len().to_u64()).to_equal(32u64)
```

</details>

### tls13_verify_data reaches interpreter

#### 32-byte HMAC over an empty transcript

1. fk push
2. var t: Transcript = transcript new
   - Expected: vd.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fk: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    fk.push(0x33u8)
    i = i + 1u64
var t: Transcript = transcript_new()
val vd = tls13_verify_data(fk, t)
expect(vd.len().to_u64()).to_equal(32u64)
```

</details>

### tls13_compute_app_secrets reaches interpreter

#### fills master_secret + c/s ap traffic from a known handshake_secret

1. hs push
2. chs push
3. shs push
4. var t: Transcript = transcript new
   - Expected: post.master_secret.len().to_u64() equals `32u64`
   - Expected: post.client_app_traffic.len().to_u64() equals `32u64`
   - Expected: post.server_app_traffic.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var hs: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    hs.push(0x55u8)
    i = i + 1u64
var chs: [u8] = []
var j: u64 = 0u64
while j < 32u64:
    chs.push(0x66u8)
    j = j + 1u64
var shs: [u8] = []
var k: u64 = 0u64
while k < 32u64:
    shs.push(0x77u8)
    k = k + 1u64
val empty: [u8] = []
var t: Transcript = transcript_new()
val pre = Tls13Secrets(
    early_secret: empty,
    handshake_secret: hs,
    master_secret: empty,
    client_hs_traffic: chs,
    server_hs_traffic: shs,
    client_app_traffic: empty,
    server_app_traffic: empty,
)
val post = tls13_compute_app_secrets(pre, t)
expect(post.master_secret.len().to_u64()).to_equal(32u64)
expect(post.client_app_traffic.len().to_u64()).to_equal(32u64)
expect(post.server_app_traffic.len().to_u64()).to_equal(32u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/_finished_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tls13_finished_key reaches interpreter
- tls13_verify_data reaches interpreter
- tls13_compute_app_secrets reaches interpreter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
