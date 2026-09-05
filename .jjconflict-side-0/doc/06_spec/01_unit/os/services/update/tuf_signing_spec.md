# TUF REAL Signature Verification Specification

> `tuf_metadata.spl` models the TUF trust structure but assumes signatures were verified elsewhere. `tuf_signing.spl` removes that assumption: signatures are checked with real Ed25519 (`os.crypto.ed25519`, pure Simple, KAT-verified byte-for-byte against RFC 8032 §7.1) over an explicitly defined canonical byte encoding, and only key-ids whose signatures ACTUALLY VERIFIED reach the structural verifier.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TUF REAL Signature Verification Specification

`tuf_metadata.spl` models the TUF trust structure but assumes signatures were verified elsewhere. `tuf_signing.spl` removes that assumption: signatures are checked with real Ed25519 (`os.crypto.ed25519`, pure Simple, KAT-verified byte-for-byte against RFC 8032 §7.1) over an explicitly defined canonical byte encoding, and only key-ids whose signatures ACTUALLY VERIFIED reach the structural verifier.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Update security |
| Status | Real cryptography (Ed25519 + SHA-256), not a model |
| Source | `test/01_unit/os/services/update/tuf_signing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`tuf_metadata.spl` models the TUF trust structure but assumes signatures were
verified elsewhere. `tuf_signing.spl` removes that assumption: signatures are
checked with real Ed25519 (`os.crypto.ed25519`, pure Simple, KAT-verified
byte-for-byte against RFC 8032 §7.1) over an explicitly defined canonical byte
encoding, and only key-ids whose signatures ACTUALLY VERIFIED reach the
structural verifier.

## Absolute oracles

- The canonical encoding is byte-exact and self-delimiting (pinned hex).
- SHA-256 of a fixed artifact equals its published digest (pinned hex).
- A correctly signed, in-date, non-rollback update is ACCEPTED.
- **Deliberate-red calibration 1** — flipping ONE byte of the signed payload
  (bumping root's version) must make a real signature stop verifying.
- **Deliberate-red calibration 2** — presenting a signature made by a DIFFERENT
  key, over the very same payload, must be rejected as a forgery.
- Untrusted keys are rejected BEFORE any cryptography runs.
- Threshold counts DISTINCT verified signers: two copies of one key's signature
  do not satisfy threshold 2.
- Every pre-existing defense (rollback, freeze, snapshot consistency) still
  fires on top of real signatures.

## Cost note

Ed25519 here runs on the interpreter (the JIT bails with
`Unknown type: u128`), so each sign or verify costs several seconds. Keys and
signatures are therefore built ONCE at module level and reused.

## Scenarios

### TUF canonical signing payload

#### u64le encodes little-endian in a fixed 8 bytes

- u64le encodes little-endian in a fixed 8 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("u64le encodes little-endian in a fixed 8 bytes")
"""Fixed width means a length prefix can never be ambiguous."""
val probe = u64le(1)
assert_eq(bytes_to_hex_lower(probe), "0100000000000000")
assert_eq(bytes_to_hex_lower(u64le(258)), "0201000000000000")
```

</details>

#### text_bytes produces ASCII bytes, not a fail-open constant

- text_bytes produces ASCII bytes, not a fail-open constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text_bytes produces ASCII bytes, not a fail-open constant")
"""`to_char_code` silently yields 0x1b; `ord` is the correct idiom."""
val probe = text_bytes("root")
assert_eq(bytes_to_hex_lower(probe), "726f6f74")
assert_eq(text_bytes("").len(), 0)
```

</details>

#### canonical_role_bytes matches its documented grammar byte-for-byte

- canonical_role_bytes matches its documented grammar byte-for-byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonical_role_bytes matches its documented grammar byte-for-byte")
"""Pinned: TUF1 | lp(role) | version | expires | threshold | rtv | lists."""
val probe = canonical_role_bytes(mk_role("root", 3, 1, ["k1"], ["k1"], 0))
val expected = "54554631" +
    "0400000000000000" + "726f6f74" +
    "0300000000000000" +
    "d007000000000000" +
    "0100000000000000" +
    "0000000000000000" +
    "0100000000000000" + "0200000000000000" + "6b31" +
    "0100000000000000" + "0200000000000000" + "6b31"
assert_eq(bytes_to_hex_lower(probe), expected)
```

</details>

#### the signed payload excludes signatures_present

- the signed payload excludes signatures_present


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the signed payload excludes signatures_present")
"""A signature cannot cover itself — adding one must not change bytes."""
val base = mk_role("targets", 11, 1, ["kA"], [], 0)
val withsig = RoleMetadata(
    role: "targets", version: 11, expires_at: 2000, threshold: 1,
    signer_key_ids: ["kA"], signatures_present: ["kA"],
    delegated_key_ids: [], recorded_targets_version: 0)
assert_eq(bytes_to_hex_lower(canonical_role_bytes(base)),
          bytes_to_hex_lower(canonical_role_bytes(withsig)))
```

</details>

#### length-prefixing prevents key-id concatenation ambiguity

- length-prefixing prevents key-id concatenation ambiguity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("length-prefixing prevents key-id concatenation ambiguity")
"""['ab','c'] and ['a','bc'] must not collide onto the same bytes."""
val one = canonical_role_bytes(mk_role("r", 1, 1, ["ab", "c"], [], 0))
val two = canonical_role_bytes(mk_role("r", 1, 1, ["a", "bc"], [], 0))
assert_true(bytes_to_hex_lower(one) != bytes_to_hex_lower(two))
```

</details>

#### role name is domain-separated from the other roles

- role name is domain-separated from the other roles


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("role name is domain-separated from the other roles")
"""Same numbers, different role, must yield a different payload."""
val a = canonical_role_bytes(mk_role("snapshot", 4, 1, ["kA"], [], 11))
val b = canonical_role_bytes(mk_role("targets", 4, 1, ["kA"], [], 11))
assert_true(bytes_to_hex_lower(a) != bytes_to_hex_lower(b))
```

</details>

#### target entries use a distinct TUFT tag

- target entries use a distinct TUFT tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("target entries use a distinct TUFT tag")
"""Role signatures can never be replayed as target signatures."""
val probe = canonical_target_bytes(
    TargetEntry(name: "img", length: 4, digest: "ab", version: 7))
assert_eq(bytes_to_hex_lower(probe).substring(0, 8), "54554654")
```

</details>

### TUF real target digests (SHA-256)
_Artifact bytes are really hashed and compared to the signed digest._

#### compute_target_digest matches the published SHA-256 vector

- compute_target_digest matches the published SHA-256 vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_target_digest matches the published SHA-256 vector")
"""SHA-256 of 01 02 03 04 — an absolute external oracle."""
val probe = compute_target_digest([1u8, 2u8, 3u8, 4u8])
assert_eq(probe, "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a")
```

</details>

#### a matching artifact passes digest verification

- a matching artifact passes digest verification


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a matching artifact passes digest verification")
"""Correct length and correct digest is accepted."""
val art = [1u8, 2u8, 3u8, 4u8]
val entry = TargetEntry(name: "img", length: 4, digest: compute_target_digest(art), version: 7)
assert_true(verify_target_digest(art, entry))
assert_true(verify_target(art, entry).accepted)
```

</details>

#### RED: one flipped artifact byte is caught by the digest

- RED: one flipped artifact byte is caught by the digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RED: one flipped artifact byte is caught by the digest")
"""The core value of real hashing — tampered payload is detected."""
val entry = TargetEntry(
    name: "img", length: 4,
    digest: compute_target_digest([1u8, 2u8, 3u8, 4u8]), version: 7)
assert_false(verify_target_digest([1u8, 2u8, 3u8, 5u8], entry))
val out = verify_target([1u8, 2u8, 3u8, 5u8], entry)
assert_false(out.accepted)
assert_eq(out.reason_code, TUF_DIGEST_MISMATCH)
```

</details>

#### a length that disagrees with the bytes is rejected

- a length that disagrees with the bytes is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a length that disagrees with the bytes is rejected")
"""Metadata that does not describe this artifact fails regardless of hash."""
val art = [1u8, 2u8, 3u8, 4u8]
val entry = TargetEntry(name: "img", length: 5, digest: compute_target_digest(art), version: 7)
assert_false(verify_target_digest(art, entry))
```

</details>

#### an empty or truncated recorded digest can never match

- an empty or truncated recorded digest can never match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty or truncated recorded digest can never match")
"""Fail closed — a missing digest is not a wildcard."""
val art = [1u8, 2u8, 3u8, 4u8]
assert_false(verify_target_digest(art, TargetEntry(name: "i", length: 4, digest: "", version: 1)))
assert_false(verify_target_digest(art, TargetEntry(name: "i", length: 4, digest: "9f64a747", version: 1)))
```

</details>

### TUF cheap rejections happen before any cryptography
_Untrusted or malformed input is denied without running a verification._

#### a signer key outside root's trusted set is rejected

- a signer key outside root's trusted set is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a signer key outside root's trusted set is rejected")
"""kB has keyring material but root never delegated it — denied first."""
val bad_root = shaped(M_ROOT, "kB", SHAPED_SIG)
val out = verify_update_signed(bad_root, S_TS, S_SNAP, S_TGT, KEYRING, CURRENT, 100)
assert_false(out.accepted)
assert_eq(out.reason_code, TUF_UNTRUSTED_KEY)
```

</details>

#### a key-id with no keyring entry is untrusted, not trusted-by-default

- a key-id with no keyring entry is untrusted, not trusted-by-default


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a key-id with no keyring entry is untrusted, not trusted-by-default")
"""No public key means it cannot be verified — fail closed, never open."""
val ring: List<TrustedKey> = [TrustedKey(key_id: "kB", public_key: PUB_B)]
val root_ok = shaped(M_ROOT, "kA", SHAPED_SIG)
val out = verify_update_signed(root_ok, S_TS, S_SNAP, S_TGT, ring, CURRENT, 100)
assert_false(out.accepted)
assert_eq(out.reason_code, TUF_UNTRUSTED_KEY)
```

</details>

#### a wrong-length signature is rejected as malformed

- a wrong-length signature is rejected as malformed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a wrong-length signature is rejected as malformed")
"""Shape is checked before Ed25519 is invoked."""
val bad_root = shaped(M_ROOT, "kA", [1u8, 2u8, 3u8])
val out = verify_update_signed(bad_root, S_TS, S_SNAP, S_TGT, KEYRING, CURRENT, 100)
assert_false(out.accepted)
assert_eq(out.reason_code, TUF_MALFORMED_SIG)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `44109d27d7552529555c95536dc617f925d7884ce926598af3dfcb7d49b34ea7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44109d27d7552529555c95536dc617f925d7884ce926598af3dfcb7d49b34ea7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44109d27d7552529555c95536dc617f925d7884ce926598af3dfcb7d49b34ea7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/services/update/tuf_signing_spec.spl
mirror: doc/06_spec/01_unit/os/services/update/tuf_signing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/update/tuf_signing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/update/tuf_signing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/update/tuf_signing_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'u64le encodes little-endian in a fixed 8 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/update/tuf_signing_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'text_bytes produces ASCII bytes, not a fail-open constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/update/tuf_signing_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'canonical_role_bytes matches its documented grammar byte-for-byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
