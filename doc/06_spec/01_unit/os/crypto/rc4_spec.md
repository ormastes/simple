# Rc4 Specification

> 1. var ct = rc4 encrypt

<!-- sdn-diagram:id=rc4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rc4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rc4_spec -> std
rc4_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rc4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rc4 Specification

## Scenarios

### RC4 — known-answer vectors

#### Key='Key', pt='Plaintext' -> BBF316E8D940AF0AD3

1. var ct = rc4 encrypt
   - Expected: _bytes_hex(ct) equals `BBF316E8D940AF0AD3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ct = rc4_encrypt(_key_key(), _pt_plaintext())
expect(_bytes_hex(ct)).to_equal("BBF316E8D940AF0AD3")
```

</details>

#### Key='Wiki', pt='pedia' -> 1021BF0420

1. var ct = rc4 encrypt
   - Expected: _bytes_hex(ct) equals `1021BF0420`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ct = rc4_encrypt(_key_wiki(), _pt_pedia())
expect(_bytes_hex(ct)).to_equal("1021BF0420")
```

</details>

#### Key='Secret', pt='Attack at dawn' -> 45A01F645FC35B383552544B9BF5

1. var ct = rc4 encrypt
   - Expected: _bytes_hex(ct) equals `45A01F645FC35B383552544B9BF5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ct = rc4_encrypt(_key_secret(), _pt_attack_at_dawn())
expect(_bytes_hex(ct)).to_equal("45A01F645FC35B383552544B9BF5")
```

</details>

#### rc4_decrypt is self-inverse of rc4_encrypt

1. var ct = rc4 encrypt
2. var pt = rc4 decrypt
   - Expected: _bytes_hex(pt) equals `_bytes_hex(_pt_attack_at_dawn())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ct = rc4_encrypt(_key_secret(), _pt_attack_at_dawn())
var pt = rc4_decrypt(_key_secret(), ct)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_pt_attack_at_dawn()))
```

</details>

#### RFC 6229: Key=0x0102030405, keystream[0:16] -> B2396305F03DC027CCC3524A0A1118A8

1. var ks = rc4 keystream
   - Expected: _bytes_hex(ks) equals `B2396305F03DC027CCC3524A0A1118A8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ks = rc4_keystream(_key_rfc6229_5byte(), 16)
expect(_bytes_hex(ks)).to_equal("B2396305F03DC027CCC3524A0A1118A8")
```

</details>

#### rc4_encrypt output length equals input length

1. var ct = rc4 encrypt
   - Expected: ct.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ct = rc4_encrypt(_key_key(), _pt_plaintext())
expect(ct.len()).to_equal(9)
```

</details>

#### rc4_init returns 256-element S-box

1. var state = rc4 init
   - Expected: state.len() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = rc4_init(_key_key())
expect(state.len()).to_equal(256)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/rc4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RC4 — known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
