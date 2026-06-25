# Ocb3 Specification

> <details>

<!-- sdn-diagram:id=ocb3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ocb3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ocb3_spec -> std
ocb3_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ocb3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ocb3 Specification

## Scenarios

### OCB3 (AES-128) — RFC 7253 Appendix A test vectors

#### TC1: empty AAD, empty PT — tag only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc1_nonce(), [], [])
expect(_bytes_to_hex(result)).to_equal(_tc1_expected_ct_tag())
```

</details>

#### TC2: 8-byte AAD, 8-byte PT — partial block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc2_nonce(), _tc2_aad(), _tc2_pt())
expect(_bytes_to_hex(result)).to_equal(_tc2_expected_ct_tag())
```

</details>

#### TC3: 8-byte AAD, empty PT — AAD-only hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc3_nonce(), _tc3_aad(), [])
expect(_bytes_to_hex(result)).to_equal(_tc3_expected_ct_tag())
```

</details>

#### TC4: empty AAD, 8-byte PT — partial block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc4_nonce(), [], _tc4_pt())
expect(_bytes_to_hex(result)).to_equal(_tc4_expected_ct_tag())
```

</details>

### OCB3 — output length contract

#### encrypt empty input yields exactly 16-byte tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc1_nonce(), [], [])
expect(result.len()).to_equal(16)
```

</details>

#### encrypt 8-byte PT yields 8 + 16 = 24 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc2_nonce(), _tc2_aad(), _tc2_pt())
expect(result.len()).to_equal(24)
```

</details>

#### encrypt 8-byte PT (TC4) yields 8 + 16 = 24 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ocb3_encrypt(_rfc7253_key(), _tc4_nonce(), [], _tc4_pt())
expect(result.len()).to_equal(24)
```

</details>

### OCB3 — decrypt error path

#### decrypt reproduces TC1 empty plaintext exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tc1_decrypt_ok()).to_equal(true)
```

</details>

#### decrypt reproduces TC2 plaintext exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tc2_decrypt_ok()).to_equal(true)
```

</details>

#### decrypt reproduces TC3 empty plaintext exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tc3_decrypt_ok()).to_equal(true)
```

</details>

#### decrypt reproduces TC4 plaintext exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tc4_decrypt_ok()).to_equal(true)
```

</details>

#### decrypt round-trips a full 16-byte block

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_full_block_rt_ok()).to_equal(true)
```

</details>

#### decrypt round-trips a partial block

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_partial_block_rt_ok()).to_equal(true)
```

</details>

#### decrypt with tampered tag returns Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tc4_decrypt_tampered_is_err()).to_equal(true)
```

</details>

#### decrypt with too-short input returns Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_short_input_is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/ocb3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OCB3 (AES-128) — RFC 7253 Appendix A test vectors
- OCB3 — output length contract
- OCB3 — decrypt error path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
