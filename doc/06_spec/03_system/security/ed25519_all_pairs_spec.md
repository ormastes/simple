# Ed25519 Cross-Vendor All-Pairs Specification

> Signs a matrix of messages with the Node reference vendor and verifies the resulting signatures through the same external reference path. Confirms deterministic Ed25519 sign+verify interoperability against a non-Simple implementation.

<!-- sdn-diagram:id=ed25519_all_pairs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ed25519_all_pairs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ed25519_all_pairs_spec -> std
ed25519_all_pairs_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ed25519_all_pairs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Cross-Vendor All-Pairs Specification

Signs a matrix of messages with the Node reference vendor and verifies the resulting signatures through the same external reference path. Confirms deterministic Ed25519 sign+verify interoperability against a non-Simple implementation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Testing |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md |
| Design | N/A |
| Research | doc/01_research/local/tls13_phase2_backlog.md |
| Source | `test/03_system/security/ed25519_all_pairs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Signs a matrix of messages with the Node reference vendor and verifies the
resulting signatures through the same external reference path. Confirms
deterministic Ed25519 sign+verify interoperability against a non-Simple
implementation.

Also:
- RFC 8032 §7.1 test vector 1 (empty message) as a fixed known-answer.
- Tampered-signature negative path: flip one bit of the signature, expect
  verify → false from every vendor.

## Out of Scope

- Pure-Simple Ed25519 sign: wraps `rt_ed25519_sign` — not pure Simple.
  Covered elsewhere by `os_rt_ed25519_sign_spec.spl`.
- Simple-server integration: blocked until server-side TLS 1.3 lands.

## Scenarios

### ed25519: RFC 8032 §7.1 TEST 1 (empty message)

#### node sign of empty msg matches the canonical signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk: [u8] = hex_to_bytes(RFC8032_SK_HEX)
val msg: [u8] = []
val sig = _unwrap_bytes(ref_ed25519_sign_via(Vendor.NODE, sk, msg))
expect(bytes_to_hex(sig)).to_equal(RFC8032_SIG_HEX)
```

</details>

#### node verify of the canonical signature returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(RFC8032_PK_HEX)
val msg: [u8] = []
val sig = hex_to_bytes(RFC8032_SIG_HEX)
expect(_unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, msg, sig))).to_equal(true)
```

</details>

### ed25519: node interop over the 8-input matrix

<details>
<summary>Advanced: node-sign → node-verify on every matrix entry</summary>

#### node-sign → node-verify on every matrix entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = hex_to_bytes(RFC8032_SK_HEX)
val pk = hex_to_bytes(RFC8032_PK_HEX)
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val msg = matrix[i]
    val sig = _unwrap_bytes(ref_ed25519_sign_via(Vendor.NODE, sk, msg))
    val ok  = _unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, msg, sig))
    expect(ok).to_equal(true)
    i = i + 1
```

</details>


</details>

### ed25519: deterministic signature agreement

<details>
<summary>Advanced: node produces byte-identical signatures over repeated matrix runs</summary>

#### node produces byte-identical signatures over repeated matrix runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = hex_to_bytes(RFC8032_SK_HEX)
val matrix = crypto_input_matrix(block_size: 64u64)
var i: u64 = 0
while i < matrix.len():
    val msg = matrix[i]
    val sig_a = _unwrap_bytes(ref_ed25519_sign_via(Vendor.NODE, sk, msg))
    val sig_b = _unwrap_bytes(ref_ed25519_sign_via(Vendor.NODE, sk, msg))
    expect(_bytes_eq(sig_a, sig_b)).to_equal(true)
    i = i + 1
```

</details>


</details>

### ed25519: tampered signature is rejected

#### node rejects a signature with its last byte flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(RFC8032_PK_HEX)
val msg: [u8] = []
val good_sig = hex_to_bytes(RFC8032_SIG_HEX)
val bad_sig = _flip_last_byte(good_sig)
expect(_unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, msg, bad_sig))).to_equal(false)
```

</details>

#### node rejects a signature from the wrong message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = hex_to_bytes(RFC8032_PK_HEX)
val wrong_msg: [u8] = [0x61u8]
val sig = hex_to_bytes(RFC8032_SIG_HEX)
expect(_unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, wrong_msg, sig))).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md](doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md)
- **Research:** [doc/01_research/local/tls13_phase2_backlog.md](doc/01_research/local/tls13_phase2_backlog.md)


</details>
