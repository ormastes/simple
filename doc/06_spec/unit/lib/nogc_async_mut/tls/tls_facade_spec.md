# Tls Facade Specification

> Tests covering nogc_async_mut TLS facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Facade Specification

## Scenarios

### nogc_async_mut TLS facades

#### re-exports TLS record and handshake builders

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports TLS record and handshake builders
   - Expected: record equals `"1603030003" + payload`
   - Expected: handshake equals `"01000003" + payload`
   - Expected: alert equals `0228`
   - Expected: is_fatal_alert(ALERT_LEVEL_FATAL) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports TLS record and handshake builders")
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

- re-exports TLS protocol name helpers
   - Expected: record_type_name(CONTENT_TYPE_HANDSHAKE) equals `Handshake`
   - Expected: tls_version_name(TLS_VERSION_1_2) equals `TLS 1.2`
   - Expected: handshake_type_name(HANDSHAKE_TYPE_CLIENT_HELLO) equals `ClientHello`
   - Expected: alert_level_name(ALERT_LEVEL_FATAL) equals `fatal`
   - Expected: alert_description_name(ALERT_DESC_HANDSHAKE_FAILURE) equals `handshake_failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports TLS protocol name helpers")
expect(record_type_name(CONTENT_TYPE_HANDSHAKE)).to_equal("Handshake")
expect(tls_version_name(TLS_VERSION_1_2)).to_equal("TLS 1.2")
expect(handshake_type_name(HANDSHAKE_TYPE_CLIENT_HELLO)).to_equal("ClientHello")
expect(alert_level_name(ALERT_LEVEL_FATAL)).to_equal("fatal")
expect(alert_description_name(ALERT_DESC_HANDSHAKE_FAILURE)).to_equal("handshake_failure")
```

</details>

#### re-exports hex formatting helpers

- re-exports hex formatting helpers
   - Expected: i64_to_hex_byte(42) equals `2a`
   - Expected: hex_len("001122") equals `3`
   - Expected: u16_be_hex(TLS_VERSION_1_2) equals `0303`
   - Expected: u24_be_hex(3) equals `000003`
   - Expected: hex_slice("0011223344", 1, 3) equals `112233`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports hex formatting helpers")
expect(i64_to_hex_byte(42)).to_equal("2a")
expect(hex_len("001122")).to_equal(3)
expect(u16_be_hex(TLS_VERSION_1_2)).to_equal("0303")
expect(u24_be_hex(3)).to_equal("000003")
expect(hex_slice("0011223344", 1, 3)).to_equal("112233")
```

</details>

#### re-exports cipher metadata helpers

- re-exports cipher metadata helpers
   - Expected: get_cipher_name(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256) equals `TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256`
   - Expected: is_cipher_suite_secure(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256) is true
   - Expected: has_forward_secrecy(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256) is true
   - Expected: is_aead_cipher(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256) is true
   - Expected: get_cipher_key_size(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256) equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports cipher metadata helpers")
expect(get_cipher_name(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal("TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256")
expect(is_cipher_suite_secure(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(true)
expect(has_forward_secrecy(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(true)
expect(is_aead_cipher(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(true)
expect(get_cipher_key_size(CIPHER_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)).to_equal(128)
```

</details>

#### re-exports hostname and constant-time comparison helpers

- re-exports hostname and constant-time comparison helpers
   - Expected: matches_hostname("*.example.com", "api.example.com") is true
   - Expected: matches_hostname("*.example.com", "example.com") is false
   - Expected: constant_time_compare("same", "same") is true
   - Expected: constant_time_compare("same", "diff") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports hostname and constant-time comparison helpers")
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
| Source | `test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut TLS facades.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7e25933c1b14650e0f2831775252f92225bd730ec06ea6ed50dd57122e8142e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7e25933c1b14650e0f2831775252f92225bd730ec06ea6ed50dd57122e8142e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7e25933c1b14650e0f2831775252f92225bd730ec06ea6ed50dd57122e8142e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/tls/tls_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/tls/tls_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/tls/tls_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports TLS record and handshake builders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports TLS protocol name helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/tls/tls_facade_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports hex formatting helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
