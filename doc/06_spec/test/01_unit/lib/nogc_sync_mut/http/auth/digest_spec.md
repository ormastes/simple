# Digest Specification

> <details>

<!-- sdn-diagram:id=digest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=digest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

digest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=digest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Digest Specification

## Scenarios

### RFC 7616 Digest SHA-256 — §3.9.1 KAT

#### response hex matches RFC 7616 §3.9.1 exact value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_header = http_digest_make_response(_rfc7616_sha256_params())
# The response= field must contain the exact 64-hex-char value from RFC
val expected_fragment = "response=\"753927fa0e85d155564e2e272a28d1802ca10daf4496794697cf8db5856cb6c1\""
expect(full_header.contains(expected_fragment)).to_equal(true)
```

</details>

#### Authorization header includes correct username

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_header = http_digest_make_response(_rfc7616_sha256_params())
expect(full_header.contains("username=\"Mufasa\"")).to_equal(true)
```

</details>

#### Authorization header includes correct realm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_header = http_digest_make_response(_rfc7616_sha256_params())
expect(full_header.contains("realm=\"http-auth@example.org\"")).to_equal(true)
```

</details>

#### Authorization header includes algorithm=SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_header = http_digest_make_response(_rfc7616_sha256_params())
expect(full_header.contains("algorithm=SHA-256")).to_equal(true)
```

</details>

### RFC 7616 Digest MD5 — §3.9.1 KAT

#### response hex matches RFC 7616 §3.9.1 MD5 exact value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_header = http_digest_make_response(_rfc7616_md5_params())
val expected_fragment = "response=\"8ca523f5e9506fed4657c9700eebdbec\""
expect(full_header.contains(expected_fragment)).to_equal(true)
```

</details>

#### Authorization header includes algorithm=MD5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_header = http_digest_make_response(_rfc7616_md5_params())
expect(full_header.contains("algorithm=MD5")).to_equal(true)
```

</details>

### RFC 7616 Digest verify — accept correct credentials

#### verify accepts correct password for SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(http_digest_verify(_rfc7616_sha256_verify_params(), "Circle of Life")).to_equal(true)
```

</details>

#### verify accepts correct password for MD5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(http_digest_verify(_rfc7616_md5_verify_params(), "Circle of Life")).to_equal(true)
```

</details>

### RFC 7616 Digest verify — tamper-reject wrong password

#### rejects wrong password for SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(not http_digest_verify(_rfc7616_sha256_verify_params(), "wrong password")).to_equal(true)
```

</details>

#### rejects wrong password for MD5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(not http_digest_verify(_rfc7616_md5_verify_params(), "wrong password")).to_equal(true)
```

</details>

#### rejects empty password for SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(not http_digest_verify(_rfc7616_sha256_verify_params(), "")).to_equal(true)
```

</details>

### RFC 7616 Digest challenge format

#### challenge includes Digest realm and nonce

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val challenge = http_digest_make_challenge(
    "http-auth@example.org",
    "7ypf/xlj9XXwfDPEoM4URrv/xwf94BcCAzFZH4GiTo0v",
    "SHA-256",
    "auth"
)
expect(challenge.starts_with("Digest ")).to_equal(true)
expect(challenge.contains("realm=\"http-auth@example.org\"")).to_equal(true)
expect(challenge.contains("nonce=\"7ypf/xlj9XXwfDPEoM4URrv/xwf94BcCAzFZH4GiTo0v\"")).to_equal(true)
expect(challenge.contains("algorithm=SHA-256")).to_equal(true)
expect(challenge.contains("qop=\"auth\"")).to_equal(true)
```

</details>

#### challenge without qop omits qop field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val challenge = http_digest_make_challenge("realm", "nonce123", "SHA-256", "")
expect(not challenge.contains("qop")).to_equal(true)
```

</details>

### RFC 7616 Digest SHA-512-256 — unsupported (FR pending)

#### make_response returns empty string for SHA-512-256 (not yet implemented)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = (
    "user", "realm", "password",
    "SHA-512-256",
    "GET", "/path",
    "nonce1", "00000001", "cnonce1", "auth"
)
expect(http_digest_make_response(params)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/http/auth/digest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RFC 7616 Digest SHA-256 — §3.9.1 KAT
- RFC 7616 Digest MD5 — §3.9.1 KAT
- RFC 7616 Digest verify — accept correct credentials
- RFC 7616 Digest verify — tamper-reject wrong password
- RFC 7616 Digest challenge format
- RFC 7616 Digest SHA-512-256 — unsupported (FR pending)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
