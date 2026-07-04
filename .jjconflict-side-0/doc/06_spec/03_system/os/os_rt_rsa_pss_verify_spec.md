# RSA-PSS Verify FFI Specification

> Structural tests for the three RSA-PSS verify FFI wrappers landed in commit `a2c5361f5e04`:

<!-- sdn-diagram:id=os_rt_rsa_pss_verify_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_rt_rsa_pss_verify_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_rt_rsa_pss_verify_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_rt_rsa_pss_verify_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RSA-PSS Verify FFI Specification

Structural tests for the three RSA-PSS verify FFI wrappers landed in commit `a2c5361f5e04`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/os/os_rt_rsa_pss_verify_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Structural tests for the three RSA-PSS verify FFI wrappers landed in commit
`a2c5361f5e04`:

  - `rsa_pss_sha256_verify(pubkey, msg, sig) -> bool`
  - `rsa_pss_sha384_verify(pubkey, msg, sig) -> bool`
  - `rsa_pss_sha512_verify(pubkey, msg, sig) -> bool`

Goal: reference-cross-check structure (design option b) so when compiled mode
lands, tests actually exercise the FFI.  In interpreter mode, `it` blocks reach
"unknown extern function: rt_rsa_pss_sha*_verify" — that is the expected state
until native compilation runs the externs.

`bin/simple check` gives load-time type-check coverage today.

tag: slow, system, crypto

## Scenarios

### rsa_pss_sha256_verify

#### accepts a valid PSS-SHA256 signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val msg  = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha256_verify(spki, msg, sig)).to_equal(true)
```

</details>

#### rejects a tampered PSS-SHA256 signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki        = hex_to_bytes(RSA_SPKI_HEX)
val sig_original = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val sig_bad     = _flip_byte(sig_original, 10)
val msg         = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha256_verify(spki, msg, sig_bad)).to_equal(false)
```

</details>

#### rejects a valid PSS-SHA256 signature with wrong message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val msg  = hex_to_bytes(WRONG_MSG_HEX)
expect(rsa_pss_sha256_verify(spki, msg, sig)).to_equal(false)
```

</details>

#### rejects a malformed SPKI for PSS-SHA256

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_spki = [0x30u8, 0x01]
val sig      = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val msg      = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha256_verify(bad_spki, msg, sig)).to_equal(false)
```

</details>

### rsa_pss_sha384_verify

#### accepts a valid PSS-SHA384 signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val msg  = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha384_verify(spki, msg, sig)).to_equal(true)
```

</details>

#### rejects a tampered PSS-SHA384 signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki         = hex_to_bytes(RSA_SPKI_HEX)
val sig_original = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val sig_bad      = _flip_byte(sig_original, 10)
val msg          = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha384_verify(spki, msg, sig_bad)).to_equal(false)
```

</details>

#### rejects a valid PSS-SHA384 signature with wrong message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val msg  = hex_to_bytes(WRONG_MSG_HEX)
expect(rsa_pss_sha384_verify(spki, msg, sig)).to_equal(false)
```

</details>

#### rejects a malformed SPKI for PSS-SHA384

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_spki = [0x30u8, 0x01]
val sig      = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val msg      = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha384_verify(bad_spki, msg, sig)).to_equal(false)
```

</details>

### rsa_pss_sha512_verify

#### accepts a valid PSS-SHA512 signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val msg  = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha512_verify(spki, msg, sig)).to_equal(true)
```

</details>

#### rejects a tampered PSS-SHA512 signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki         = hex_to_bytes(RSA_SPKI_HEX)
val sig_original = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val sig_bad      = _flip_byte(sig_original, 10)
val msg          = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha512_verify(spki, msg, sig_bad)).to_equal(false)
```

</details>

#### rejects a valid PSS-SHA512 signature with wrong message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val msg  = hex_to_bytes(WRONG_MSG_HEX)
expect(rsa_pss_sha512_verify(spki, msg, sig)).to_equal(false)
```

</details>

#### rejects a malformed SPKI for PSS-SHA512

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_spki = [0x30u8, 0x01]
val sig      = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val msg      = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha512_verify(bad_spki, msg, sig)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
