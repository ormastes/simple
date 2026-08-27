# Ed25519 Cross-Vendor All-Pairs Specification

> Signs a matrix of messages with the Node reference vendor and verifies the resulting signatures through the same external reference path. Confirms deterministic Ed25519 sign+verify interoperability against a non-Simple implementation.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- node sign of empty msg matches the canonical signature
   - Expected: bytes_to_hex(sig) equals `RFC8032_SIG_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node sign of empty msg matches the canonical signature")
val sk: [u8] = hex_to_bytes(RFC8032_SK_HEX)
val msg: [u8] = []
val sig = _unwrap_bytes(ref_ed25519_sign_via(Vendor.NODE, sk, msg))
expect(bytes_to_hex(sig)).to_equal(RFC8032_SIG_HEX)
```

</details>

#### node verify of the canonical signature returns true

- node verify of the canonical signature returns true
   - Expected: _unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, msg, sig)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node verify of the canonical signature returns true")
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

- node-sign → node-verify on every matrix entry
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node-sign → node-verify on every matrix entry")
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

- node produces byte-identical signatures over repeated matrix runs
   - Expected: _bytes_eq(sig_a, sig_b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node produces byte-identical signatures over repeated matrix runs")
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

- node rejects a signature with its last byte flipped
   - Expected: _unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, msg, bad_sig)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node rejects a signature with its last byte flipped")
val pk = hex_to_bytes(RFC8032_PK_HEX)
val msg: [u8] = []
val good_sig = hex_to_bytes(RFC8032_SIG_HEX)
val bad_sig = _flip_last_byte(good_sig)
expect(_unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, msg, bad_sig))).to_equal(false)
```

</details>

#### node rejects a signature from the wrong message

- node rejects a signature from the wrong message
   - Expected: _unwrap_bool(ref_ed25519_verify_via(Vendor.NODE, pk, wrong_msg, sig)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("node rejects a signature from the wrong message")
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

- **Plan:** `doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md`
- **Research:** `doc/01_research/local/tls13_phase2_backlog.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38591028b680ccbbf15d6364462a8b8cf42cf0c25f54b376d0344fdde81dc7c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38591028b680ccbbf15d6364462a8b8cf42cf0c25f54b376d0344fdde81dc7c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38591028b680ccbbf15d6364462a8b8cf42cf0c25f54b376d0344fdde81dc7c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/security/ed25519_all_pairs_spec.spl
mirror: doc/06_spec/03_system/security/ed25519_all_pairs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/ed25519_all_pairs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/ed25519_all_pairs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/ed25519_all_pairs_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node sign of empty msg matches the canonical signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/ed25519_all_pairs_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node verify of the canonical signature returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/ed25519_all_pairs_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'node-sign → node-verify on every matrix entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
