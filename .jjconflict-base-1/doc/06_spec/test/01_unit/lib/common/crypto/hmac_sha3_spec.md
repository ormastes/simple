# Hmac Sha3 Specification

> <details>

<!-- sdn-diagram:id=hmac_sha3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hmac_sha3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hmac_sha3_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hmac_sha3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hmac Sha3 Specification

## Scenarios

### HMAC-SHA3-256 — published reference vectors

#### TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = ba85192310dffa96e2a3a40e69774351140bb7185e1202cdcc917589f95e16bb
expect(bytes_to_hex(hmac_sha3_256_bytes(_bytes_repeat(0x0b, 20), _hi_there()))).to_equal(
    "ba85192310dffa96e2a3a40e69774351140bb7185e1202cdcc917589f95e16bb"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = c7d4072e788877ae3596bbb0da73b887c9171f93095b294ae857fbe2645e1ba5
expect(bytes_to_hex(hmac_sha3_256("Jefe", "what do ya want for nothing?"))).to_equal(
    "c7d4072e788877ae3596bbb0da73b887c9171f93095b294ae857fbe2645e1ba5"
)
```

</details>

### HMAC-SHA3-384 — published reference vectors

#### TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = 68d2dcf7fd4ddd0a2240c8a437305f61fb7334cfb5d0226e1bc27dc1
#       0a2e723a20d370b47743130e26ac7e3d532886bd
expect(bytes_to_hex(hmac_sha3_384_bytes(_bytes_repeat(0x0b, 20), _hi_there()))).to_equal(
    "68d2dcf7fd4ddd0a2240c8a437305f61fb7334cfb5d0226e1bc27dc10a2e723a20d370b47743130e26ac7e3d532886bd"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = f1101f8cbf9766fd6764d2ed61903f21ca9b18f57cf3e1a23ca13508a93243ce
#       48c045dc007f26a21b3f5e0e9df4c20a
expect(bytes_to_hex(hmac_sha3_384("Jefe", "what do ya want for nothing?"))).to_equal(
    "f1101f8cbf9766fd6764d2ed61903f21ca9b18f57cf3e1a23ca13508a93243ce48c045dc007f26a21b3f5e0e9df4c20a"
)
```

</details>

### HMAC-SHA3-512 — published reference vectors

#### TC1: K=20*0x0b, M='Hi There' (NIST CAVP / Wycheproof)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = eb3fbd4b2eaab8f5c504bd3a41465aacec15770a7cabac531e482f86
#       0b5ec7ba47ccb2c6f2afce8f88d22b6dc61380f23
#       a668fd3888bb80537c0a0b86407689e
expect(bytes_to_hex(hmac_sha3_512_bytes(_bytes_repeat(0x0b, 20), _hi_there()))).to_equal(
    "eb3fbd4b2eaab8f5c504bd3a41465aacec15770a7cabac531e482f860b5ec7ba47ccb2c6f2afce8f88d22b6dc61380f23a668fd3888bb80537c0a0b86407689e"
)
```

</details>

#### TC2: K='Jefe', M='what do ya want for nothing?'

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MAC = 5a4bfeab6166427c7a3647b747292b8384537cdb89afb3bf5665e4c5e
#       709350b287baec921fd7ca0ee7a0c31d022a95e1
#       fc92ba9d77df883960275beb4e62024
expect(bytes_to_hex(hmac_sha3_512("Jefe", "what do ya want for nothing?"))).to_equal(
    "5a4bfeab6166427c7a3647b747292b8384537cdb89afb3bf5665e4c5e709350b287baec921fd7ca0ee7a0c31d022a95e1fc92ba9d77df883960275beb4e62024"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hmac_sha3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HMAC-SHA3-256 — published reference vectors
- HMAC-SHA3-384 — published reference vectors
- HMAC-SHA3-512 — published reference vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
