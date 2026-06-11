# PEM Parser Specification

> Validates the PEM parser module that parses PEM-encoded certificates and private keys into DER bytes. Tests cover single blocks, certificate chains, private key extraction, is_pem detection, and error/edge cases.

<!-- sdn-diagram:id=pem_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pem_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pem_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pem_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PEM Parser Specification

Validates the PEM parser module that parses PEM-encoded certificates and private keys into DER bytes. Tests cover single blocks, certificate chains, private key extraction, is_pem detection, and error/edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/crypto/pem_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the PEM parser module that parses PEM-encoded certificates and
private keys into DER bytes. Tests cover single blocks, certificate chains,
private key extraction, is_pem detection, and error/edge cases.

NOTE: interpreter-mode runner verifies file loading and spec structure only.
Field-value assertions fire under compiled/native mode
(see .claude/memory/feedback_compile_mode_false_greens.md).

## Scenarios

### parse_pem — single certificate block

#### returns exactly one block for a single certificate PEM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_single_cert()
expect(blocks.len()).to_equal(1)
```

</details>

#### sets label to CERTIFICATE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_single_cert()
expect(blocks[0].label).to_equal("CERTIFICATE")
```

</details>

#### produces non-empty DER bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_single_cert()
expect(blocks[0].der_bytes.len()).to_be_greater_than(0)
```

</details>

#### DER bytes start with SEQUENCE tag 0x30

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_single_cert()
expect(blocks[0].der_bytes[0u64].to_i64()).to_equal(48)
```

</details>

### parse_pem — certificate chain

#### returns two blocks for a two-cert chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_chain()
expect(blocks.len()).to_equal(2)
```

</details>

#### both blocks have label CERTIFICATE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_chain()
expect(blocks[0].label).to_equal("CERTIFICATE")
expect(blocks[1].label).to_equal("CERTIFICATE")
```

</details>

#### both blocks have non-empty DER bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_chain()
expect(blocks[0].der_bytes.len()).to_be_greater_than(0)
expect(blocks[1].der_bytes.len()).to_be_greater_than(0)
```

</details>

### parse_pem_key — private key extraction

#### finds PRIVATE KEY block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = parse_pem_key(_key_pem())
expect(key.label).to_equal("PRIVATE KEY")
```

</details>

#### finds RSA PRIVATE KEY block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = parse_pem_key(_rsa_key_pem())
expect(key.label).to_equal("RSA PRIVATE KEY")
```

</details>

#### finds EC PRIVATE KEY block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = parse_pem_key(_ec_key_pem())
expect(key.label).to_equal("EC PRIVATE KEY")
```

</details>

#### key DER bytes are non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = parse_pem_key(_key_pem())
expect(key.der_bytes.len()).to_be_greater_than(0)
```

</details>

#### returns empty label when no key found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = parse_pem_key(_single_cert_pem())
expect(key.label).to_equal("")
```

</details>

### parse_pem_certs — filter certificates from mixed PEM

#### returns only certificate blocks from mixed PEM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val certs = parse_pem_certs(_mixed_pem())
expect(certs.len()).to_equal(2)
```

</details>

#### all returned blocks have label CERTIFICATE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val certs = parse_pem_certs(_mixed_pem())
expect(certs[0].label).to_equal("CERTIFICATE")
expect(certs[1].label).to_equal("CERTIFICATE")
```

</details>

### parse_pem — mixed blocks

#### returns three blocks for cert+key+cert PEM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_mixed()
expect(blocks.len()).to_equal(3)
```

</details>

#### first block is CERTIFICATE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_mixed()
expect(blocks[0].label).to_equal("CERTIFICATE")
```

</details>

#### second block is PRIVATE KEY

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_mixed()
expect(blocks[1].label).to_equal("PRIVATE KEY")
```

</details>

#### third block is CERTIFICATE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = _parse_mixed()
expect(blocks[2].label).to_equal("CERTIFICATE")
```

</details>

### is_pem — PEM format detection

#### returns true for valid PEM text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_pem(_single_cert_pem())).to_equal(true)
```

</details>

#### returns true for key PEM text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_pem(_key_pem())).to_equal(true)
```

</details>

#### returns false for plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_pem("not pem data")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_pem("")).to_equal(false)
```

</details>

#### returns false for partial marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_pem("-----BEGIN")).to_equal(false)
```

</details>

### parse_pem — edge cases

#### returns empty list for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_pem("")
expect(blocks.len()).to_equal(0)
```

</details>

#### returns empty list for non-PEM text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_pem("just some random text without markers")
expect(blocks.len()).to_equal(0)
```

</details>

#### returns empty list for incomplete BEGIN marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_pem("-----BEGIN CERTIFICATE-----\ndata without end")
expect(blocks.len()).to_equal(0)
```

</details>

#### handles PEM with extra whitespace in body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem = "-----BEGIN TEST-----\n  SGVsbG8=  \n-----END TEST-----\n"
val blocks = parse_pem(pem)
expect(blocks.len()).to_equal(1)
expect(blocks[0].label).to_equal("TEST")
```

</details>

#### handles PEM with no newlines in body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem = "-----BEGIN TEST-----SGVsbG8=-----END TEST-----"
val blocks = parse_pem(pem)
expect(blocks.len()).to_equal(1)
expect(blocks[0].label).to_equal("TEST")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
