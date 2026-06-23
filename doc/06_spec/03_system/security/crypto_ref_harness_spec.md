# Crypto Reference Harness Specification

> Self-test for test/system/crypto_ref_harness.spl cross-vendor dispatch. Verifies that OPENSSL and NODE return the same bytes for the RFC-6234 SHA-256 fixtures and for the RFC-7748 X25519 test vector.

<!-- sdn-diagram:id=crypto_ref_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crypto_ref_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crypto_ref_harness_spec -> std
crypto_ref_harness_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crypto_ref_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val got = _unwrap_ok(ref_sha256_via(Vendor.NODE, empty))
expect(bytes_to_hex(got)).to_equal(SHA256_EMPTY_HEX)
```

</details>

#### node SHA-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got = _unwrap_ok(ref_sha256_via(Vendor.NODE, [0x61u8, 0x62u8, 0x63u8]))
expect(bytes_to_hex(got)).to_equal(SHA256_ABC_HEX)
```

</details>

### crypto_ref_harness: cross-vendor SHA-256 matrix

<details>
<summary>Advanced: openssl and node agree on every matrix entry</summary>

#### openssl and node agree on every matrix entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = [0x6bu8, 0x65u8, 0x79u8]
val msg = hex_to_bytes("54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67")
val got = _unwrap_ok(ref_hmac_sha256_via(Vendor.NODE, key, msg))
expect(bytes_to_hex(got)).to_equal(HMAC_SHA256_KEY_FOX_HEX)
```

</details>

### crypto_ref_harness: X25519 RFC 7748 §5.2 vector 1

#### node matches the expected shared secret

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = hex_to_bytes(X25519_SCALAR_HEX)
val peer   = hex_to_bytes(X25519_PEER_HEX)
val got    = _unwrap_ok(ref_x25519_via(Vendor.NODE, scalar, peer))
expect(bytes_to_hex(got)).to_equal(X25519_SHARED_HEX)
```

</details>

### crypto_ref_harness: supported vendors do real work

#### node SHA-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input: [u8] = [0x61u8]
val got = _unwrap_ok(ref_sha256_via(Vendor.NODE, input))
expect(bytes_to_hex(got)).to_equal("ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb")
```

</details>

#### node X25519 agrees with the RFC vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = hex_to_bytes(X25519_SCALAR_HEX)
val peer   = hex_to_bytes(X25519_PEER_HEX)
val node   = _unwrap_ok(ref_x25519_via(Vendor.NODE, scalar, peer))
expect(bytes_to_hex(node)).to_equal(X25519_SHARED_HEX)
```

</details>

### crypto_ref_harness: vendor_name returns canonical tag

#### returns lowercase names for known vendors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
