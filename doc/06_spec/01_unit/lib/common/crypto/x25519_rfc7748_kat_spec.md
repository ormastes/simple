# X25519 key agreement — RFC 7748 known-answer vectors

> X25519 is the key-agreement primitive behind TLS 1.3 and SSH key exchange in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519 key agreement — RFC 7748 known-answer vectors

X25519 is the key-agreement primitive behind TLS 1.3 and SSH key exchange in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

X25519 is the key-agreement primitive behind TLS 1.3 and SSH key exchange in
this tree. Everyone who relies on those transports relies on this function
returning the one shared secret RFC 7748 defines — not merely 32 plausible
bytes. This scenario is the reproducing case for
`doc/08_tracking/bug/x25519_extern_not_registered_interp_2026-06-15.md`, which
was closed as "source fixed" without anyone ever running the arithmetic.

## Scope and Preconditions

Covers the pure-Simple Montgomery ladder in
`src/lib/nogc_async_mut_noalloc/tls/x25519.spl`, which is the sole X25519
implementation — there is no runtime extern to fall back to. No host
capability, network, or hardware is required.

## Primary Workflow

An operator agreeing a key supplies a 32-byte private scalar and the peer's
32-byte u-coordinate, and receives a 32-byte shared secret. The scenario pins
that output against the RFC's own vectors, then checks the property that makes
key agreement useful at all: both sides must independently arrive at the same
secret.

## Key Concepts

| Concept | Description |
|---------|-------------|
| RFC 7748 5.2 | Scalar-multiplication vector: fixed scalar and u give one defined output |
| RFC 7748 6.1 | Alice's private key maps to one defined public key on base point 9 |
| DH agreement | `x25519(a, pub_b)` must equal `x25519(b, pub_a)` |

## Evidence and Provenance

Expected values are transcribed from RFC 7748 sections 5.2 and 6.1. They are
external to this repository and cannot be satisfied by any self-consistent but
incorrect implementation — which is exactly how the original defect survived.

## Recovery and Troubleshooting

A wrong hex value here means the field arithmetic or the ladder is broken, not
the test. Do not adjust the expected constants: they are the standard. Probe
the field layer first (round-trip, `a * a^-1 == 1`, `2^100 * 2^50 == 2^150`),
then the ladder's starting state.

## Compatibility and Limitations

Runs anywhere the interpreter runs. Timing side channels are out of scope.

## Scenarios

### X25519 scalar multiplication reproduces RFC 7748 5.2

#### derives the shared secret the standard defines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives the shared secret the standard defines
- Supply the RFC 7748 5.2 private scalar and peer u-coordinate
- Read back the 32-byte shared secret as hex
   - Expected: _shared_5_2() equals `c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives the shared secret the standard defines")
step("Supply the RFC 7748 5.2 private scalar and peer u-coordinate")
step("Read back the 32-byte shared secret as hex")
# The value below is RFC 7748 5.2's stated output. Before the field
# arithmetic was corrected this returned 23af31d7...3600 — note the
# trailing 00, the signature of a serializer that emitted 31 real
# bytes and padded the last one.
expect(_shared_5_2()).to_equal("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")
```

</details>

#### returns exactly 32 bytes

- returns exactly 32 bytes
- Confirm the secret is a full 256-bit value
   - Expected: x25519(_rfc7748_5_2_scalar(), _rfc7748_5_2_u()).length() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns exactly 32 bytes")
step("Confirm the secret is a full 256-bit value")
expect(x25519(_rfc7748_5_2_scalar(), _rfc7748_5_2_u()).length()).to_equal(32)
```

</details>

### X25519 public-key derivation reproduces RFC 7748 6.1

#### maps Alice's private key to her published public key

- maps Alice's private key to her published public key
- Multiply Alice's private scalar by the curve base point 9
   - Expected: _alice_public() equals `8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Alice's private key to her published public key")
step("Multiply Alice's private scalar by the curve base point 9")
expect(_alice_public()).to_equal("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
```

</details>

#### maps Bob's private key to his published public key

- maps Bob's private key to his published public key
- Multiply Bob's private scalar by the curve base point 9
   - Expected: _bob_public() equals `de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Bob's private key to his published public key")
step("Multiply Bob's private scalar by the curve base point 9")
expect(_bob_public()).to_equal("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
```

</details>

### X25519 key agreement converges from both sides

#### gives both parties the same secret

- gives both parties the same secret
- Alice combines her private key with Bob's public key
- Bob combines his private key with Alice's public key
   - Expected: _alice_side_secret() equals `_bob_side_secret()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives both parties the same secret")
# A ladder can be self-consistent and still wrong, so the RFC vectors
# above are the primary oracle. This case adds the property that makes
# the primitive usable: the two independently computed secrets agree.
# It was 'no' while the ladder started from a zeroed x_3.
step("Alice combines her private key with Bob's public key")
step("Bob combines his private key with Alice's public key")
expect(_alice_side_secret()).to_equal(_bob_side_secret())
```

</details>

#### agrees on the secret RFC 7748 6.1 publishes

- agrees on the secret RFC 7748 6.1 publishes
- Compare the agreed secret against the standard's stated value
   - Expected: _alice_side_secret() equals `4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees on the secret RFC 7748 6.1 publishes")
step("Compare the agreed secret against the standard's stated value")
expect(_alice_side_secret()).to_equal("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-CRYPTO-X25519-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3439c32532d30056b141a7ca8a1badcd2cdd9dfed11c8117d6050000639e4767`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3439c32532d30056b141a7ca8a1badcd2cdd9dfed11c8117d6050000639e4767`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3439c32532d30056b141a7ca8a1badcd2cdd9dfed11c8117d6050000639e4767`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives the shared secret the standard defines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exactly 32 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Alice's private key to her published public key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
