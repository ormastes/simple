# Tls Io Record Specification

> <details>

<!-- sdn-diagram:id=tls_io_record_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls_io_record_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls_io_record_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls_io_record_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Io Record Specification

## Scenarios

### TLS record hex parser

#### parses a TLS 1.2 handshake record

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_record_hex("1603030003616263")
expect(parsed.is_ok()).to_be(true)
val view = parsed.unwrap()
expect(view.content_type).to_equal(CONTENT_TYPE_HANDSHAKE)
expect(view.version).to_equal(TLS_VERSION_1_2)
expect(view.payload_len).to_equal(3)
expect(view.payload_hex).to_equal("616263")
```

</details>

#### parses a TLS 1.2 application data record for HTTPS payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_record_hex("1703030012474554202f20485454502f312e310d0a0d0a")
expect(parsed.is_ok()).to_be(true)
val view = parsed.unwrap()
expect(view.content_type).to_equal(CONTENT_TYPE_APPLICATION_DATA)
expect(view.payload_hex).to_contain("474554202f20485454502f312e31")
```

</details>

#### rejects short TLS record headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_record_hex("16030300")
expect(parsed.is_err()).to_be(true)
expect(parsed.err().unwrap()).to_equal("tls record header too short")
```

</details>

#### rejects unsupported TLS record content types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_record_hex("6303030003616263")
expect(parsed.is_err()).to_be(true)
expect(parsed.err().unwrap()).to_equal("tls record content type unsupported")
```

</details>

#### rejects unsupported TLS record versions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_record_hex("1603040003616263")
expect(parsed.is_err()).to_be(true)
expect(parsed.err().unwrap()).to_equal("tls record version unsupported")
```

</details>

#### rejects mismatched TLS record lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_record_hex("1603030004616263")
expect(parsed.is_err()).to_be(true)
expect(parsed.err().unwrap()).to_equal("tls record length mismatch")
```

</details>

#### parses a TLS record header before the payload is read

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = parse_record_header_hex("1703030012")
expect(header.is_ok()).to_be(true)
val view = header.unwrap()
expect(view.content_type).to_equal(CONTENT_TYPE_APPLICATION_DATA)
expect(view.version).to_equal(TLS_VERSION_1_2)
expect(view.payload_len).to_equal(18)
```

</details>

#### rejects oversized TLS record headers before reading payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = parse_record_header_hex("1703034001")
expect(header.is_err()).to_be(true)
expect(header.err().unwrap()).to_equal("tls record payload too large")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tls/tls_io_record_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS record hex parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
