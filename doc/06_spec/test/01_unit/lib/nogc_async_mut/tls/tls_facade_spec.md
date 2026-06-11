# Tls Facade Specification

> <details>

<!-- sdn-diagram:id=tls_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Facade Specification

## Scenarios

### nogc_async_mut TLS facades

#### re-exports TLS record and handshake builders

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "010203"
val record = build_tls_record_hex(CONTENT_TYPE_HANDSHAKE, TLS_VERSION_1_2, payload)
expect(record).to_equal("1603030003" + payload)

val handshake = build_handshake_message_hex(HANDSHAKE_TYPE_CLIENT_HELLO, payload)
expect(handshake).to_equal("01000003" + payload)

val alert = build_alert_hex(ALERT_LEVEL_FATAL, ALERT_DESC_HANDSHAKE_FAILURE)
expect(alert).to_equal("0228")
expect(is_fatal_alert(ALERT_LEVEL_FATAL)).to_equal(true)
```

</details>

#### re-exports TLS protocol name helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(record_type_name(CONTENT_TYPE_HANDSHAKE)).to_equal("Handshake")
expect(tls_version_name(TLS_VERSION_1_2)).to_equal("TLS 1.2")
expect(handshake_type_name(HANDSHAKE_TYPE_CLIENT_HELLO)).to_equal("ClientHello")
expect(alert_level_name(ALERT_LEVEL_FATAL)).to_equal("fatal")
expect(alert_description_name(ALERT_DESC_HANDSHAKE_FAILURE)).to_equal("handshake_failure")
```

</details>

#### re-exports hex formatting helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i64_to_hex_byte(42)).to_equal("2a")
expect(hex_len("001122")).to_equal(3)
expect(u16_be_hex(TLS_VERSION_1_2)).to_equal("0303")
expect(u24_be_hex(3)).to_equal("000003")
expect(hex_slice("0011223344", 1, 3)).to_equal("112233")
```

</details>

#### re-exports cipher metadata helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_cipher_name(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal("TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256")
expect(is_cipher_suite_secure(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(true)
expect(has_forward_secrecy(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(true)
expect(is_aead_cipher(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(true)
expect(get_cipher_key_size(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(128)
```

</details>

#### re-exports hostname and constant-time comparison helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(matches_hostname("*.example.com", "api.example.com")).to_equal(true)
expect(matches_hostname("*.example.com", "example.com")).to_equal(false)
expect(constant_time_compare("same", "same")).to_equal(true)
expect(constant_time_compare("same", "diff")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tls/tls_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut TLS facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
