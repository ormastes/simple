# Crypto Reference Harness Specification

> Self-test for test/system/crypto_ref_harness.spl cross-vendor dispatch. Verifies that OPENSSL and NODE return the same bytes for the RFC-6234 SHA-256 fixtures and for the RFC-7748 X25519 test vector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crypto Reference Harness Specification

Self-test for test/system/crypto_ref_harness.spl cross-vendor dispatch. Verifies that OPENSSL and NODE return the same bytes for the RFC-6234 SHA-256 fixtures and for the RFC-7748 X25519 test vector.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Testing |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/security/crypto_ref_harness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Self-test for test/system/crypto_ref_harness.spl cross-vendor dispatch.
Verifies that OPENSSL and NODE return the same bytes for the
RFC-6234 SHA-256 fixtures and for the RFC-7748 X25519 test vector.

Requires the host to have at least openssl and node >=20 installed and
recorded in tools/ref_crypto/manifest.json.

## Scenarios

### crypto_ref_harness: ref_sha256_via RFC-6234

#### node SHA-256(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- node SHA-256(\
   - Expected: bytes_to_hex(got) equals `SHA256_EMPTY_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node SHA-256(\")
val empty: [u8] = []
val got = _unwrap_ok(ref_sha256_via(Vendor.NODE, empty))
expect(bytes_to_hex(got)).to_equal(SHA256_EMPTY_HEX)
```

</details>

#### node SHA-256(\

- node SHA-256(\
   - Expected: bytes_to_hex(got) equals `SHA256_ABC_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node SHA-256(\")
val got = _unwrap_ok(ref_sha256_via(Vendor.NODE, [0x61u8, 0x62u8, 0x63u8]))
expect(bytes_to_hex(got)).to_equal(SHA256_ABC_HEX)
```

</details>

### crypto_ref_harness: cross-vendor SHA-256 matrix

<details>
<summary>Advanced: openssl and node agree on every matrix entry</summary>

#### openssl and node agree on every matrix entry

- openssl and node agree on every matrix entry
   - Expected: a equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("openssl and node agree on every matrix entry")
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val input = matrix[i]
    val a = bytes_to_hex(_unwrap_ok(ref_sha256_via(Vendor.OPENSSL, input)))
    val c = bytes_to_hex(_unwrap_ok(ref_sha256_via(Vendor.NODE, input)))
    expect(a).to_equal(c)
    i = i + 1
```

</details>


</details>

### crypto_ref_harness: HMAC-SHA256 external reference

#### node HMAC-SHA256(key=\

- node HMAC-SHA256(key=\
   - Expected: bytes_to_hex(got) equals `HMAC_SHA256_KEY_FOX_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node HMAC-SHA256(key=\")
val key = [0x6bu8, 0x65u8, 0x79u8]
val msg = hex_to_bytes("54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67")
val got = _unwrap_ok(ref_hmac_sha256_via(Vendor.NODE, key, msg))
expect(bytes_to_hex(got)).to_equal(HMAC_SHA256_KEY_FOX_HEX)
```

</details>

### crypto_ref_harness: X25519 RFC 7748 §5.2 vector 1

#### node matches the expected shared secret

- node matches the expected shared secret
   - Expected: bytes_to_hex(got) equals `X25519_SHARED_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node matches the expected shared secret")
val scalar = hex_to_bytes(X25519_SCALAR_HEX)
val peer   = hex_to_bytes(X25519_PEER_HEX)
val got    = _unwrap_ok(ref_x25519_via(Vendor.NODE, scalar, peer))
expect(bytes_to_hex(got)).to_equal(X25519_SHARED_HEX)
```

</details>

### crypto_ref_harness: supported vendors do real work

#### node SHA-256(\

- node SHA-256(\
   - Expected: bytes_to_hex(got) equals `ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node SHA-256(\")
val input: [u8] = [0x61u8]
val got = _unwrap_ok(ref_sha256_via(Vendor.NODE, input))
expect(bytes_to_hex(got)).to_equal("ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb")
```

</details>

#### node X25519 agrees with the RFC vector

- node X25519 agrees with the RFC vector
   - Expected: bytes_to_hex(node) equals `X25519_SHARED_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node X25519 agrees with the RFC vector")
val scalar = hex_to_bytes(X25519_SCALAR_HEX)
val peer   = hex_to_bytes(X25519_PEER_HEX)
val node   = _unwrap_ok(ref_x25519_via(Vendor.NODE, scalar, peer))
expect(bytes_to_hex(node)).to_equal(X25519_SHARED_HEX)
```

</details>

### crypto_ref_harness: vendor_name returns canonical tag

#### returns lowercase names for known vendors

- returns lowercase names for known vendors
   - Expected: vendor_name(Vendor.OPENSSL) equals `openssl`
   - Expected: vendor_name(Vendor.NODE) equals `node`
   - Expected: vendor_name(Vendor.RING) equals `ring`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns lowercase names for known vendors")
expect(vendor_name(Vendor.OPENSSL)).to_equal("openssl")
expect(vendor_name(Vendor.NODE)).to_equal("node")
expect(vendor_name(Vendor.RING)).to_equal("ring")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `318a9386486054d2496f058bbfaf7069c8328dbc426338cab8f2a6b8fa9f165d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `318a9386486054d2496f058bbfaf7069c8328dbc426338cab8f2a6b8fa9f165d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `318a9386486054d2496f058bbfaf7069c8328dbc426338cab8f2a6b8fa9f165d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/security/crypto_ref_harness_spec.spl
mirror: doc/06_spec/03_system/security/crypto_ref_harness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/crypto_ref_harness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/crypto_ref_harness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/crypto_ref_harness_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node SHA-256(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/crypto_ref_harness_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node SHA-256(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/crypto_ref_harness_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'openssl and node agree on every matrix entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
