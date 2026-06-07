# X509 Specification

> <details>

<!-- sdn-diagram:id=x509_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x509_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x509_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x509_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X509 Specification

## Scenarios

### x509_parse_der — parse valid ECDSA P-256 self-signed cert

#### returns Ok for the known-good test certificate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_result_is_ok(_parse_test_cert())).to_equal(true)
```

</details>

#### parses version as 2 (v3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.version).to_equal(2)
```

</details>

#### parses serial number as single byte 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.serial.len()).to_equal(1)
expect(cert.serial[0u64].to_i64()).to_equal(1)
```

</details>

#### parses signature algorithm OID as ecdsa-with-SHA256 (1.2.840.10045.4.3.2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
# OID arcs: [1, 2, 840, 10045, 4, 3, 2]
expect(cert.sig_alg_oid.len()).to_equal(7)
expect(cert.sig_alg_oid[0]).to_equal(1)
expect(cert.sig_alg_oid[1]).to_equal(2)
expect(cert.sig_alg_oid[2]).to_equal(840)
expect(cert.sig_alg_oid[6]).to_equal(2)
```

</details>

#### subject CN equals 'test'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(x509_cert_cn(cert)).to_equal("test")
```

</details>

#### issuer CN equals 'test' (self-signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(x509_cert_issuer_cn(cert)).to_equal("test")
```

</details>

#### parses SPKI algorithm OID as id-ecPublicKey (1.2.840.10045.2.1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
# OID arcs: [1, 2, 840, 10045, 2, 1]
expect(cert.spki_alg_oid.len()).to_equal(6)
expect(cert.spki_alg_oid[0]).to_equal(1)
expect(cert.spki_alg_oid[3]).to_equal(10045)
expect(cert.spki_alg_oid[4]).to_equal(2)
```

</details>

#### spki_key is non-empty (65 bytes for uncompressed P-256 point)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.spki_key.len()).to_equal(65)
```

</details>

#### not_before_unix is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.not_before_unix > 0).to_equal(true)
```

</details>

#### not_after_unix is greater than not_before_unix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.not_after_unix > cert.not_before_unix).to_equal(true)
```

</details>

#### not_before year is 2026 (unix ts in range 2026-01-01 .. 2027-01-01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
# 2026-01-01 00:00:00 UTC = 1767225600
# 2027-01-01 00:00:00 UTC = 1798761600
expect(cert.not_before_unix > 1767225600).to_equal(true)
expect(cert.not_before_unix < 1798761600).to_equal(true)
```

</details>

#### has 3 extensions (SubjectKeyId, AuthorityKeyId, BasicConstraints)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.extensions.len()).to_equal(3)
```

</details>

#### sig_value is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.sig_value.len() > 0).to_equal(true)
```

</details>

### x509_parse_der — error cases

#### returns Err for a truncated (3-byte) input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_result_is_err(x509_parse_der(_truncated_der()))).to_equal(true)
```

</details>

#### error reason contains 'InvalidDer' for truncated input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = _result_reason(x509_parse_der(_truncated_der()))
expect(reason.contains("InvalidDer")).to_equal(true)
```

</details>

#### returns Err for wrong outer tag (0x01 instead of 0x30)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_result_is_err(x509_parse_der(_wrong_outer_tag_der()))).to_equal(true)
```

</details>

#### returns Err for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_result_is_err(x509_parse_der([]))).to_equal(true)
```

</details>

### x509_parse_pem — PEM wrapper

#### returns Err for a string with no PEM markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_result_is_err(x509_parse_pem("not a pem string"))).to_equal(true)
```

</details>

#### error reason contains 'InvalidPem' for missing markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = _result_reason(x509_parse_pem("no markers here"))
expect(reason.contains("InvalidPem")).to_equal(true)
```

</details>

### x509 civil-to-epoch — validity date sanity

#### not_before is non-negative for the test cert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
expect(cert.not_before_unix >= 0).to_equal(true)
```

</details>

#### not_after is approximately 10 years after not_before

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = _test_cert_ok()
# 10 years ≈ 315360000 seconds; cert is 3650 days = 315360000s
val diff = cert.not_after_unix - cert.not_before_unix
expect(diff > 315000000).to_equal(true)
expect(diff < 316000000).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cert/x509_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x509_parse_der — parse valid ECDSA P-256 self-signed cert
- x509_parse_der — error cases
- x509_parse_pem — PEM wrapper
- x509 civil-to-epoch — validity date sanity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
