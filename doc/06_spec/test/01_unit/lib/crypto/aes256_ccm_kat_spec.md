# Aes256 Ccm Kat Specification

> <details>

<!-- sdn-diagram:id=aes256_ccm_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes256_ccm_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes256_ccm_kat_spec -> std
aes256_ccm_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes256_ccm_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Ccm Kat Specification

## Scenarios

### AES-256-CCM NIST CAVP VADT256 byte-exact vectors

#### V1 encrypt (Alen=0): CT matches NIST CAVP Count=0 Plen=24 Nlen=13 Tlen=16

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), [], _v1_plaintext(), 16)
expect(out.len()).to_equal(40)  # 24 PT + 16 tag
val ct = _split_ct(out, 24)
val tag = _split_tag(out, 24, 16)
expect(ct).to_equal(_v1_expected_ct())
expect(tag).to_equal(_v1_expected_tag())
```

</details>

#### V1 decrypt (Alen=0): correct tag returns original plaintext

1.  v1 expected ct
2. Aes256CcmResult Ok
   - Expected: data equals `_v1_plaintext()`
3. Aes256CcmResult Err
   - Expected: msg equals `"")  # unreachable: CAVP vector must verify`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes256_ccm_decrypt(_v1_key(), _v1_nonce(), [],
                                _v1_expected_ct(), _v1_expected_tag())
match result:
    Aes256CcmResult.Ok(data):
        expect(data).to_equal(_v1_plaintext())
    Aes256CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: CAVP vector must verify
```

</details>

#### V1 decrypt: corrupted tag is rejected

1.  v1 expected ct
2. Aes256CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable`
3. Aes256CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All-FF tag guaranteed != real tag; no XOR/indexing to avoid Value::U8 push pitfall
val bad_tag = _hex_to_bytes("ffffffffffffffffffffffffffffffff")
val result = aes256_ccm_decrypt(_v1_key(), _v1_nonce(), [],
                                _v1_expected_ct(), bad_tag)
match result:
    Aes256CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable
    Aes256CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

#### V2 encrypt (Alen=32): CT matches NIST CAVP Count=320 Plen=24 Nlen=13 Tlen=16

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v2_key(), _v2_nonce(), _v2_aad(), _v2_plaintext(), 16)
expect(out.len()).to_equal(40)  # 24 PT + 16 tag
val ct = _split_ct(out, 24)
val tag = _split_tag(out, 24, 16)
expect(ct).to_equal(_v2_expected_ct())
expect(tag).to_equal(_v2_expected_tag())
```

</details>

#### V2 decrypt (Alen=32): correct tag returns original plaintext

1.  v2 expected ct
2. Aes256CcmResult Ok
   - Expected: data equals `_v2_plaintext()`
3. Aes256CcmResult Err
   - Expected: msg equals `"")  # unreachable: CAVP vector must verify`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = aes256_ccm_decrypt(_v2_key(), _v2_nonce(), _v2_aad(),
                                _v2_expected_ct(), _v2_expected_tag())
match result:
    Aes256CcmResult.Ok(data):
        expect(data).to_equal(_v2_plaintext())
    Aes256CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: CAVP vector must verify
```

</details>

#### V2 decrypt: modified AAD is rejected

1. var bad aad: [u8] = rt array new with cap
2. bad aad push
3.  v2 expected ct
4. Aes256CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable`
5. Aes256CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad_aad: [u8] = rt_array_new_with_cap(32)
var i: u64 = 0
while i < 32:
    bad_aad.push(0xFF)
    i = i + 1
val result = aes256_ccm_decrypt(_v2_key(), _v2_nonce(), bad_aad,
                                _v2_expected_ct(), _v2_expected_tag())
match result:
    Aes256CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable
    Aes256CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

### AES-256-CCM encrypt→decrypt round-trip

#### V3 round-trip: 12-byte AAD, 19-byte PT, M=8

1. Aes256CcmResult Ok
   - Expected: data equals `_v3_plaintext()`
2. Aes256CcmResult Err
   - Expected: msg equals `"")  # unreachable: round-trip must succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_plaintext(), 8)
expect(out.len()).to_equal(27)  # 19 PT + 8 tag
val ct = _split_ct(out, 19)
val tag = _split_tag(out, 19, 8)
val result = aes256_ccm_decrypt(_v3_key(), _v3_nonce(), _v3_aad(), ct, tag)
match result:
    Aes256CcmResult.Ok(data):
        expect(data).to_equal(_v3_plaintext())
    Aes256CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable: round-trip must succeed
```

</details>

#### V3 round-trip: corrupted tag is rejected

1. Aes256CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable`
2. Aes256CcmResult Err
   - Expected: msg contains `tag mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_plaintext(), 8)
val ct = _split_ct(out, 19)
# All-FF 8-byte tag guaranteed != real tag; avoids Value::U8 push pitfall
val bad_tag = _hex_to_bytes("ffffffffffffffff")
val result = aes256_ccm_decrypt(_v3_key(), _v3_nonce(), _v3_aad(), ct, bad_tag)
match result:
    Aes256CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable
    Aes256CcmResult.Err(msg):
        expect(msg.contains("tag mismatch")).to_equal(true)
```

</details>

#### V4 round-trip: empty plaintext, empty AAD, M=8 (tag-only)

1. Aes256CcmResult Ok
   - Expected: data.len() equals `0)  # empty plaintext`
2. Aes256CcmResult Err
   - Expected: msg equals `"")  # unreachable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v4_key(), _v4_nonce(), [], [], 8)
expect(out.len()).to_equal(8)  # 0 PT + 8 tag
val ct = _split_ct(out, 0)
val tag = _split_tag(out, 0, 8)
val result = aes256_ccm_decrypt(_v4_key(), _v4_nonce(), [], ct, tag)
match result:
    Aes256CcmResult.Ok(data):
        expect(data.len()).to_equal(0)  # empty plaintext
    Aes256CcmResult.Err(msg):
        expect(msg).to_equal("")  # unreachable
```

</details>

### AES-256-CCM parameter validation

#### wrong key length (16 bytes instead of 32) returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_key = _hex_to_bytes("26511fb51fcfa75cb4b44da75a6e5a0e")
val out = aes256_ccm_encrypt(bad_key, _v1_nonce(), [], _v1_plaintext(), 16)
expect(out.len()).to_equal(0)
```

</details>

#### wrong nonce length (11 bytes instead of 13) returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_nonce = _hex_to_bytes("72a60f345a1978fb40f28a")
val out = aes256_ccm_encrypt(_v1_key(), bad_nonce, [], _v1_plaintext(), 16)
expect(out.len()).to_equal(0)
```

</details>

#### odd tag length returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), [], _v1_plaintext(), 7)
expect(out.len()).to_equal(0)
```

</details>

#### decrypt wrong key length returns Err with message

1.  v1 expected ct
2. Aes256CcmResult Ok
   - Expected: data.len() equals `99999)  # unreachable`
3. Aes256CcmResult Err
   - Expected: msg contains `32 bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_key = _hex_to_bytes("26511fb51fcfa75cb4b44da75a6e5a0e")
val result = aes256_ccm_decrypt(bad_key, _v1_nonce(), [],
                                _v1_expected_ct(), _v1_expected_tag())
match result:
    Aes256CcmResult.Ok(data):
        expect(data.len()).to_equal(99999)  # unreachable
    Aes256CcmResult.Err(msg):
        expect(msg.contains("32 bytes")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes256_ccm_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-256-CCM NIST CAVP VADT256 byte-exact vectors
- AES-256-CCM encrypt→decrypt round-trip
- AES-256-CCM parameter validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
