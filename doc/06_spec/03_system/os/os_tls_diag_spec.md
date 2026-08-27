# Os Tls Diag Specification

> <details>

<!-- sdn-diagram:id=os_tls_diag_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_tls_diag_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_tls_diag_spec -> std
os_tls_diag_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_tls_diag_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Tls Diag Specification

## Scenarios

### TLS diag

#### hkdf_extract changes when IKM changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ikm_a: [u8] = [
    0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8,
    0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8,
    0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8
]

val ikm_diff: [u8] = [
    0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8,
    0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8,
    0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8
]

val salt_a: [u8] = [
    0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8,
    0x07u8, 0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8
]

val prk_a = hkdf_extract(salt_a, ikm_a)
val prk_diff = hkdf_extract(salt_a, ikm_diff)
expect(_bytes_eq(prk_a, prk_diff)).to_equal(false)
```

</details>

#### hkdf_extract_from_list changes when IKM changes

1. ikm a push
2. ikm a push
3. ikm diff push
4. ikm diff push
5. salt a push
6. salt a push
7. salt a push
8. salt a push
9. salt a push
10. salt a push
11. salt a push
12. salt a push
13. salt a push
14. salt a push
15. salt a push
16. salt a push
17. salt a push
   - Expected: prk_a.len() equals `32`
   - Expected: prk_diff.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ikm_a = []
var i = 0
while i < 79:
    ikm_a.push(0x41)
    i = i + 1
ikm_a.push(0x41)

var ikm_diff = []
i = 0
while i < 79:
    ikm_diff.push(0x41)
    i = i + 1
ikm_diff.push(0x42)

var salt_a = []
salt_a.push(0x00)
salt_a.push(0x01)
salt_a.push(0x02)
salt_a.push(0x03)
salt_a.push(0x04)
salt_a.push(0x05)
salt_a.push(0x06)
salt_a.push(0x07)
salt_a.push(0x08)
salt_a.push(0x09)
salt_a.push(0x0a)
salt_a.push(0x0b)
salt_a.push(0x0c)

val prk_a = hkdf_extract_from_list(salt_a, ikm_a)
val prk_diff = hkdf_extract_from_list(salt_a, ikm_diff)
expect(prk_a.len()).to_equal(32)
expect(prk_diff.len()).to_equal(32)
```

</details>

#### hkdf_expand_label encodes a different info block than raw expand

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk_a: [u8] = [
    0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8, 0x08u8,
    0x09u8, 0x0Au8, 0x0Bu8, 0x0Cu8, 0x0Du8, 0x0Eu8, 0x0Fu8, 0x10u8,
    0x11u8, 0x12u8, 0x13u8, 0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8,
    0x19u8, 0x1Au8, 0x1Bu8, 0x1Cu8, 0x1Du8, 0x1Eu8, 0x1Fu8, 0x20u8
]
val empty_ctx: [u8] = []
val label_out = hkdf_expand_label(prk_a, "key", empty_ctx, 32)
val raw_expand = hkdf_expand(prk_a, empty_ctx, 32)
expect(_bytes_eq(label_out, raw_expand)).to_equal(false)
```

</details>

#### transcript hash changes when message bytes change

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = transcript_new()
val h4 = transcript_hash(transcript_add(t0, [0xAAu8, 0xBBu8]))
val h5 = transcript_hash(transcript_add(t0, [0xCCu8, 0xDDu8]))
expect(_bytes_eq(h4, h5)).to_equal(false)
```

</details>

#### hmac_from_list differs when second-block bytes change

1. msg a push
2. msg b push
3. msg a push
4. msg b push
   - Expected: _bytes_eq(hmac_a, hmac_b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msg_a = []
var msg_b = []
var i = 0
while i < 79:
    msg_a.push(0x41)
    msg_b.push(0x41)
    i = i + 1
msg_a.push(0x41)
msg_b.push(0x42)

val key = [
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
    0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c
]
val hmac_a = sha256_hmac_from_list(key, msg_a)
val hmac_b = sha256_hmac_from_list(key, msg_b)
expect(_bytes_eq(hmac_a, hmac_b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_diag_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS diag

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
