# Ed25519 Operation Message Regression Specification

> Tests covering pure Ed25519 operation-message interoperability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Operation Message Regression Specification

## Scenarios

### pure Ed25519 operation-message interoperability

#### matches RFC 8032 test vector 1 exactly and verifies it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches RFC 8032 test vector 1 exactly and verifies it
   - Expected: hex_u8(public_key) equals `d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a`
   - Expected: hex_u8(signature) equals `e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33... (full value in folded executable source)`
   - Expected: pure_ed25519_verify(public_key, [], signature) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches RFC 8032 test vector 1 exactly and verifies it")
val seed = from_hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
val public_key = ed25519_pubkey(seed)
expect(hex_u8(public_key)).to_equal("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
val signature = pure_ed25519_sign(seed, public_key, [])
expect(hex_u8(signature)).to_equal("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
expect(pure_ed25519_verify(public_key, [], signature)).to_equal(true)
```

</details>

#### reduces and multiplies the operation nonce to the canonical R point

- reduces and multiplies the operation nonce to the canonical R point
   - Expected: hex_bytes(sha512_bytes([for b in operation_message(): b.to_i64()])) equals `eb7696bf32fc49e01d5793c27f0dae8c711315b88b70c6ce49bfc9c79f697b7355869c6d7ce25... (full value in folded executable source)`
   - Expected: hex_bytes(sha512_bytes(nonce_input)) equals `5a44d446555653e92fc79b2eaf442a1bb616f2d20d1d4e7bc9a86fca6a319cdd273e4970fbce8... (full value in folded executable source)`
   - Expected: operation_message().len() equals `1021`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reduces and multiplies the operation nonce to the canonical R point")
expect(hex_bytes(sha512_bytes([for b in operation_message(): b.to_i64()]))).to_equal("eb7696bf32fc49e01d5793c27f0dae8c711315b88b70c6ce49bfc9c79f697b7355869c6d7ce257b504b83009fc22641f38bd2fbd5d0125fa327cbf0c06915b23")
val seed_hash = sha512_bytes([for b in seed7(): b.to_i64()])
var nonce_input: [i64] = []
var i = 32
while i < 64:
    nonce_input.push(seed_hash[i])
    i = i + 1
for b in operation_message(): nonce_input.push(b.to_i64())
expect(hex_bytes(sha512_bytes(nonce_input))).to_equal("5a44d446555653e92fc79b2eaf442a1bb616f2d20d1d4e7bc9a86fca6a319cdd273e4970fbce8e21b5e42b146adcafa22c7d44a203318516193ac471e4b8d60a")
expect(operation_message().len()).to_equal(1021)
```

</details>

#### matches the canonical operation-message signature and verifies it

- matches the canonical operation-message signature and verifies it
   - Expected: hex_u8(public_key) equals `ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c`
   - Expected: hex_u8(signature) equals `1fcf7554e9ddce9ead7ca4280560936909511bc7c468aa74d0e35d0fe1312ca0ba5115f1220b8... (full value in folded executable source)`
   - Expected: pure_ed25519_verify(public_key, operation_message(), signature) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the canonical operation-message signature and verifies it")
val seed = seed7()
val public_key = ed25519_pubkey(seed)
expect(hex_u8(public_key)).to_equal("ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c")
val signature = pure_ed25519_sign(seed, public_key, operation_message())
expect(hex_u8(signature)).to_equal("1fcf7554e9ddce9ead7ca4280560936909511bc7c468aa74d0e35d0fe1312ca0ba5115f1220b82e69d53c79cf82e93acb790bce44142ea4acc93fcb1aa21580e")
expect(pure_ed25519_verify(public_key, operation_message(), signature)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure Ed25519 operation-message interoperability.
- pure Ed25519 operation-message interoperability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdca711aa8cf784ea3653b2533cfec494430a74bc38ffe1a67c7436f15527102`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdca711aa8cf784ea3653b2533cfec494430a74bc38ffe1a67c7436f15527102`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdca711aa8cf784ea3653b2533cfec494430a74bc38ffe1a67c7436f15527102`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches RFC 8032 test vector 1 exactly and verifies it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reduces and multiplies the operation nonce to the canonical R point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/ed25519_operation_message_regression_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the canonical operation-message signature and verifies it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
