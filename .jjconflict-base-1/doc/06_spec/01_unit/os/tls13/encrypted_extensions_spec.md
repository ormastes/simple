# Encrypted Extensions Specification

> 1. fail

<!-- sdn-diagram:id=encrypted_extensions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encrypted_extensions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encrypted_extensions_spec -> std
encrypted_extensions_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encrypted_extensions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encrypted Extensions Specification

## Scenarios

### parse_encrypted_extensions happy paths

#### accepts an empty extensions list

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_empty())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.server_name_acknowledged).to_equal(false)
    expect(value.selected_alpn).to_equal("")
    expect(value.max_fragment_length).to_equal(0u8)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### records server_name acknowledgement

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_server_name_ack())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.server_name_acknowledged).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### extracts the selected ALPN protocol

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_alpn_h2())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.selected_alpn).to_equal("h2")
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### ignores unknown extension types and continues parsing

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_unknown_then_alpn())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.selected_alpn).to_equal("h2")
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### echoes max_fragment_length byte

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_mfl())
if val EncryptedExtensionsResult.Ok(value) = res:
    expect(value.max_fragment_length).to_equal(0x04u8)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

### parse_encrypted_extensions rejections

#### rejects duplicate extension_type as illegal_parameter

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_dup_sni())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### rejects truncated body as decode_error

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_truncated_outer())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("decode_error")).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### rejects non-empty server_name in EE

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_server_name_nonempty())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### rejects early_data extension (0-RTT not implemented)

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_early_data())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("unsupported_extension")).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### rejects ALPN with multiple ProtocolNames

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_alpn_two_names())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

#### rejects malformed max_fragment_length

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_encrypted_extensions(_ee_mfl_bad_len())
if val EncryptedExtensionsResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
else:
    fail("unexpected TLS13 EncryptedExtensions parse branch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/encrypted_extensions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_encrypted_extensions happy paths
- parse_encrypted_extensions rejections

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
