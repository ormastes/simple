# Hmac Sha1 Specification

> <details>

<!-- sdn-diagram:id=hmac_sha1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hmac_sha1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hmac_sha1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hmac_sha1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hmac Sha1 Specification

## Scenarios

### HMAC-SHA-1 — RFC 2202 §3 reference vectors

#### TC1: K=20*0x0b, M='Hi There'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = b617318655057264e28bc0b6fb378c8ef146be00
expect(bytes_to_hex(hmac_sha1_bytes(_bytes_repeat(0x0b, 20), [0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65]))).to_equal(
    "b617318655057264e28bc0b6fb378c8ef146be00"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = effcdf6ae5eb2fa2d27416d5f184df9c259a7c79
expect(bytes_to_hex(hmac_sha1("Jefe", "what do ya want for nothing?"))).to_equal(
    "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"
)
```

</details>

#### TC3: K=20*0xaa, M=50*0xdd

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = 125d7342b9ac11cd91a39af48aa17b4f63f175d3
expect(bytes_to_hex(hmac_sha1_bytes(_bytes_repeat(0xaa, 20), _bytes_repeat(0xdd, 50)))).to_equal(
    "125d7342b9ac11cd91a39af48aa17b4f63f175d3"
)
```

</details>

#### TC4: K=25-byte 0x01..0x19, M=50*0xcd

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = 4c9007f4026250c6bc8414f9bf50c86c2d7235da
expect(bytes_to_hex(hmac_sha1_bytes(_tc4_key(), _bytes_repeat(0xcd, 50)))).to_equal(
    "4c9007f4026250c6bc8414f9bf50c86c2d7235da"
)
```

</details>

#### TC6: K=80*0xaa (longer than block), short data — exercises inner-hash key path

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'Test Using Larger Than Block-Size Key - Hash Key First'
# MAC = aa4ae5e15272d00e95705637ce8a3b55ed402112
val msg = [
    0x54, 0x65, 0x73, 0x74, 0x20, 0x55, 0x73, 0x69, 0x6e, 0x67, 0x20, 0x4c, 0x61, 0x72, 0x67, 0x65,
    0x72, 0x20, 0x54, 0x68, 0x61, 0x6e, 0x20, 0x42, 0x6c, 0x6f, 0x63, 0x6b, 0x2d, 0x53, 0x69, 0x7a,
    0x65, 0x20, 0x4b, 0x65, 0x79, 0x20, 0x2d, 0x20, 0x48, 0x61, 0x73, 0x68, 0x20, 0x4b, 0x65, 0x79,
    0x20, 0x46, 0x69, 0x72, 0x73, 0x74
]
expect(bytes_to_hex(hmac_sha1_bytes(_bytes_repeat(0xaa, 80), msg))).to_equal(
    "aa4ae5e15272d00e95705637ce8a3b55ed402112"
)
```

</details>

### HMAC-SHA-1 — output shape

#### MAC is exactly 20 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hmac_sha1("k", "m").len()).to_equal(20)
```

</details>

#### hex form is exactly 40 chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hmac_sha1("k", "m")).len()).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hmac_sha1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HMAC-SHA-1 — RFC 2202 §3 reference vectors
- HMAC-SHA-1 — output shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
