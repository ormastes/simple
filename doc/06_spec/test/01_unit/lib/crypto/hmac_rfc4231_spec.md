# Hmac Rfc4231 Specification

> <details>

<!-- sdn-diagram:id=hmac_rfc4231_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hmac_rfc4231_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hmac_rfc4231_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hmac_rfc4231_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hmac Rfc4231 Specification

## Scenarios

### HMAC-SHA-256 RFC 4231 test vectors

#### TC1 short key + 'Hi There' → b0344c61...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.2: b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7
expect(bytes_to_hex(hmac_sha256_bytes(_tc1_key(), _tc1_data()))).to_equal(
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
)
```

</details>

#### TC2 'Jefe' key + 'what do ya want for nothing?' → 5bdcc146...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.3: 5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843
expect(bytes_to_hex(hmac_sha256_bytes(_tc2_key(), _tc2_data()))).to_equal(
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
)
```

</details>

#### TC3 20×0xaa key + 50×0xdd → 773ea91e...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.4: 773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe
expect(bytes_to_hex(hmac_sha256_bytes(_tc3_key(), _tc3_data()))).to_equal(
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"
)
```

</details>

#### TC4 25-byte key + 50×0xcd → 82558a38...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.5: 82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b
expect(bytes_to_hex(hmac_sha256_bytes(_tc4_key(), _tc4_data()))).to_equal(
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"
)
```

</details>

#### TC6 131×0xaa key + 54-byte data → 60e43159...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.7: 60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54
expect(bytes_to_hex(hmac_sha256_bytes(_tc6_key(), _tc6_data()))).to_equal(
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
)
```

</details>

#### TC7 131×0xaa key + 152-byte data → 9b09ffa7...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.8: 9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2
expect(bytes_to_hex(hmac_sha256_bytes(_tc7_key(), _tc7_data()))).to_equal(
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"
)
```

</details>

### HMAC-SHA-512 RFC 4231 test vectors

#### TC1 short key + 'Hi There' → 87aa7cde...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.2: 87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854
expect(bytes_to_hex(hmac_sha512_bytes(_tc1_key(), _tc1_data()))).to_equal(
    "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"
)
```

</details>

#### TC2 'Jefe' key + 'what do ya want for nothing?' → 164b7a7b...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.3: 164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737
expect(bytes_to_hex(hmac_sha512_bytes(_tc2_key(), _tc2_data()))).to_equal(
    "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"
)
```

</details>

#### TC3 20×0xaa key + 50×0xdd → fa73b008...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.4: fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb
expect(bytes_to_hex(hmac_sha512_bytes(_tc3_key(), _tc3_data()))).to_equal(
    "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb"
)
```

</details>

#### TC4 25-byte key + 50×0xcd → b0ba4656...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.5: b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd
expect(bytes_to_hex(hmac_sha512_bytes(_tc4_key(), _tc4_data()))).to_equal(
    "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd"
)
```

</details>

#### TC6 131×0xaa key + 54-byte data → 80b24263...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.7: 80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598
expect(bytes_to_hex(hmac_sha512_bytes(_tc6_key(), _tc6_data()))).to_equal(
    "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"
)
```

</details>

#### TC7 131×0xaa key + 152-byte data → e37b6a77...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 4231 §4.8: e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58
expect(bytes_to_hex(hmac_sha512_bytes(_tc7_key(), _tc7_data()))).to_equal(
    "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/hmac_rfc4231_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HMAC-SHA-256 RFC 4231 test vectors
- HMAC-SHA-512 RFC 4231 test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
