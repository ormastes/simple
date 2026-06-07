# Tls Common Hooks Aes Gcm Specification

> <details>

<!-- sdn-diagram:id=tls_common_hooks_aes_gcm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls_common_hooks_aes_gcm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls_common_hooks_aes_gcm_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls_common_hooks_aes_gcm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Common Hooks Aes Gcm Specification

## Scenarios

### TLS common AES-GCM hooks

#### encrypts NIST TC2 through pure Simple AES-GCM

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val plaintext_hex = "00000000000000000000000000000000"
val aad_hex = ""
val expected_hex = "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf"

val actual_hex = tls_hook_aes_gcm_encrypt_hex(key_hex, nonce_hex, plaintext_hex, aad_hex)

expect(actual_hex).to_equal(expected_hex)
```

</details>

#### decrypts NIST TC2 through pure Simple AES-GCM

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val ciphertext_hex = "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf"
val aad_hex = ""

val actual_hex = tls_hook_aes_gcm_decrypt_hex(key_hex, nonce_hex, ciphertext_hex, aad_hex)

if actual_hex == nil:
    expect("decrypt should return plaintext").to_equal("")
else:
    expect(actual_hex).to_equal("00000000000000000000000000000000")
```

</details>

#### decrypts valid empty plaintext distinctly from authentication failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val ciphertext_hex = "58e2fccefa7e3061367f1d57a4e7455a"
val aad_hex = ""

val actual_hex = tls_hook_aes_gcm_decrypt_hex(key_hex, nonce_hex, ciphertext_hex, aad_hex)

if actual_hex == nil:
    expect("empty plaintext should not be nil").to_equal("")
else:
    expect(actual_hex).to_equal("")
```

</details>

#### rejects invalid tags without calling runtime AES-GCM externs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val ciphertext_hex = "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bd20"
val aad_hex = ""

val actual_hex = tls_hook_aes_gcm_decrypt_hex(key_hex, nonce_hex, ciphertext_hex, aad_hex)

expect(actual_hex).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS common AES-GCM hooks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
