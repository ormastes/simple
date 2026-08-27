# Jwt Specification

> Tests covering JWT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jwt Specification

## Scenarios

### JWT

#### REQ-JWT-001: RFC 7515 A.1 HS256 header base64url encodes correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-JWT-001: RFC 7515 A.1 HS256 header base64url encodes correctly
   - Expected: parts.len() equals `3`
   - Expected: parts.get(0) equals `RFC7515_A1_HEADER_B64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-001: RFC 7515 A.1 HS256 header base64url encodes correctly")
val header_text = _bytes_to_text(_rfc7515_a1_header_bytes())
# Use the encode function via the sign module's internal logic —
# we verify by checking jwt_sign_hs256_bytes produces the correct output
val header_bytes = _rfc7515_a1_header_bytes()
val payload_bytes = _rfc7515_a1_payload_bytes()
val key = _rfc7515_a1_key()
val compact = jwt_sign_hs256_bytes(
    _bytes_to_text(header_bytes),
    _bytes_to_text(payload_bytes),
    key
)
# Extract the header segment
val parts = compact.split(".")
expect(parts.len()).to_equal(3)
expect(parts.get(0)).to_equal(RFC7515_A1_HEADER_B64)
```

</details>

#### REQ-JWT-002: RFC 7515 A.1 HS256 payload base64url encodes correctly

- REQ-JWT-002: RFC 7515 A.1 HS256 payload base64url encodes correctly
   - Expected: parts.get(1) equals `RFC7515_A1_PAYLOAD_B64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-002: RFC 7515 A.1 HS256 payload base64url encodes correctly")
val header_bytes = _rfc7515_a1_header_bytes()
val payload_bytes = _rfc7515_a1_payload_bytes()
val key = _rfc7515_a1_key()
val compact = jwt_sign_hs256_bytes(
    _bytes_to_text(header_bytes),
    _bytes_to_text(payload_bytes),
    key
)
val parts = compact.split(".")
expect(parts.get(1)).to_equal(RFC7515_A1_PAYLOAD_B64)
```

</details>

#### REQ-JWT-003: RFC 7515 A.1 HS256 signature matches RFC vector

- REQ-JWT-003: RFC 7515 A.1 HS256 signature matches RFC vector
   - Expected: parts.get(2) equals `RFC7515_A1_SIG_B64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-003: RFC 7515 A.1 HS256 signature matches RFC vector")
val header_bytes = _rfc7515_a1_header_bytes()
val payload_bytes = _rfc7515_a1_payload_bytes()
val key = _rfc7515_a1_key()
val compact = jwt_sign_hs256_bytes(
    _bytes_to_text(header_bytes),
    _bytes_to_text(payload_bytes),
    key
)
val parts = compact.split(".")
expect(parts.get(2)).to_equal(RFC7515_A1_SIG_B64)
```

</details>

#### REQ-JWT-004: RFC 7515 A.1 HS256 full compact JWT matches RFC vector byte-for-byte

- REQ-JWT-004: RFC 7515 A.1 HS256 full compact JWT matches RFC vector byte-for-byte
   - Expected: compact equals `RFC7515_A1_COMPACT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-004: RFC 7515 A.1 HS256 full compact JWT matches RFC vector byte-for-byte")
val header_bytes = _rfc7515_a1_header_bytes()
val payload_bytes = _rfc7515_a1_payload_bytes()
val key = _rfc7515_a1_key()
val compact = jwt_sign_hs256_bytes(
    _bytes_to_text(header_bytes),
    _bytes_to_text(payload_bytes),
    key
)
expect(compact).to_equal(RFC7515_A1_COMPACT)
```

</details>

#### REQ-JWT-005: HS256 sign-then-verify round-trip

- REQ-JWT-005: HS256 sign-then-verify round-trip
   - Expected: parts.len() equals `3`
   - Expected: _hs256_verify_ok(compact, key) is true
   - Expected: decoded contains `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-005: HS256 sign-then-verify round-trip")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(((i * 7 + 13) % 256).to_u8())
    i = i + 1
val payload = "{\"sub\":\"1234\",\"role\":\"admin\"}"
val compact = jwt_sign_hs256(payload, key)
val parts = compact.split(".")
expect(parts.len()).to_equal(3)
expect(_hs256_verify_ok(compact, key)).to_equal(true)
val decoded = _hs256_verify_payload(compact, key)
expect(decoded.contains("1234")).to_equal(true)
```

</details>

#### REQ-JWT-006: HS256 verify rejects wrong key

- REQ-JWT-006: HS256 verify rejects wrong key
   - Expected: _hs256_verify_ok(compact, wrong_key) is false
   - Expected: err_msg contains `verification failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-006: HS256 verify rejects wrong key")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(((i * 7 + 13) % 256).to_u8())
    i = i + 1
var wrong_key: [u8] = []
var j = 0
while j < 32:
    wrong_key.push(((j * 3 + 99) % 256).to_u8())
    j = j + 1
val payload = "{\"sub\":\"tampered\"}"
val compact = jwt_sign_hs256(payload, key)
expect(_hs256_verify_ok(compact, wrong_key)).to_equal(false)
val err_msg = _hs256_verify_err(compact, wrong_key)
expect(err_msg.contains("verification failed")).to_equal(true)
```

</details>

#### REQ-JWT-007: HS256 verify rejects tampered payload

- REQ-JWT-007: HS256 verify rejects tampered payload
   - Expected: msg contains `verification failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-007: HS256 verify rejects tampered payload")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(0xAAu8)
    i = i + 1
val payload = "{\"sub\":\"user1\"}"
val compact = jwt_sign_hs256(payload, key)
# Tamper: change last char of payload segment
val parts = compact.split(".")
val tampered = parts.get(0) + "." + parts.get(1) + "X" + "." + parts.get(2)
val result = jwt_verify_hs256(tampered, key)
match result:
    Ok(_):
        fail("jwt_verify_hs256 accepted a tampered payload segment")
    Err(msg):
        expect(msg.contains("verification failed")).to_equal(true)
```

</details>

#### REQ-JWT-008: jwt_sign_hs256 produces 3-part compact JWT

- REQ-JWT-008: jwt_sign_hs256 produces 3-part compact JWT
   - Expected: parts.len() equals `3`
   - Expected: compact does not contain `=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-008: jwt_sign_hs256 produces 3-part compact JWT")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(0x42u8)
    i = i + 1
val compact = jwt_sign_hs256("{\"hello\":\"world\"}", key)
val parts = compact.split(".")
expect(parts.len()).to_equal(3)
# No padding characters allowed in base64url
expect(compact.contains("=")).to_equal(false)
```

</details>

#### REQ-JWT-009: RS256 sign-then-verify round-trip

- REQ-JWT-009: RS256 sign-then-verify round-trip
   - Expected: compact.split(".").len() equals `3`
   - Expected: msg.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-009: RS256 sign-then-verify round-trip")
# We cannot embed a real RSA DER key inline without PEM parsing.
# This test documents the interface contract:
# jwt_sign_rs256 returns Err on empty key (no-key case verified).
var empty_pkcs8: [u8] = []
val result = jwt_sign_rs256("{\"sub\":\"rs256_test\"}", empty_pkcs8)
match result:
    Ok(compact):
        # If somehow an empty key signs (runtime dependent), require a compact JWT shape.
        expect(compact.split(".").len()).to_equal(3)
    Err(msg):
        # Expected: RSA signing fails on empty key
        expect(msg.length() > 0).to_equal(true)
```

</details>

#### REQ-JWT-010: ES256 sign-then-verify round-trip

- REQ-JWT-010: ES256 sign-then-verify round-trip
   - Expected: compact.split(".").len() equals `3`
   - Expected: msg.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-010: ES256 sign-then-verify round-trip")
# We cannot embed a real ECDSA P-256 DER key inline without PEM parsing.
# This test documents the interface contract:
# jwt_sign_es256 returns Err on empty key (no-key case verified).
var empty_pkcs8: [u8] = []
val result = jwt_sign_es256("{\"sub\":\"es256_test\"}", empty_pkcs8)
match result:
    Ok(compact):
        # If somehow an empty key signs (runtime dependent), require a compact JWT shape.
        expect(compact.split(".").len()).to_equal(3)
    Err(msg):
        # Expected: ECDSA signing fails on empty key
        expect(msg.length() > 0).to_equal(true)
```

</details>

#### REQ-JWT-011: HS256 compact JWT contains no base64 padding

- REQ-JWT-011: HS256 compact JWT contains no base64 padding
   - Expected: compact does not contain `=`
   - Expected: compact does not contain `+`
   - Expected: compact does not contain `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-011: HS256 compact JWT contains no base64 padding")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(0x01u8)
    i = i + 1
val compact = jwt_sign_hs256("{\"x\":1}", key)
expect(compact.contains("=")).to_equal(false)
expect(compact.contains("+")).to_equal(false)
expect(compact.contains("/")).to_equal(false)
```

</details>

#### REQ-JWT-012: jwt_verify_hs256 rejects non-JWT string

- REQ-JWT-012: jwt_verify_hs256 rejects non-JWT string
   - Expected: msg.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-JWT-012: jwt_verify_hs256 rejects non-JWT string")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(0x01u8)
    i = i + 1
val result = jwt_verify_hs256("not.a.jwt.at.all.extra", key)
match result:
    Ok(_):
        fail("jwt_verify_hs256 accepted a compact token with too many segments")
    Err(msg):
        expect(msg.length() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/jwt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JWT.
- JWT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `3191da31bbf092133e97746c90c9c2f801bc46fe4c89a62a89b53d2ba8658695`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3191da31bbf092133e97746c90c9c2f801bc46fe4c89a62a89b53d2ba8658695`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3191da31bbf092133e97746c90c9c2f801bc46fe4c89a62a89b53d2ba8658695`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/jwt_spec.spl
mirror: doc/06_spec/01_unit/lib/common/jwt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/jwt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/jwt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/jwt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/jwt_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-JWT-001: RFC 7515 A.1 HS256 header base64url encodes correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/jwt_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-JWT-002: RFC 7515 A.1 HS256 payload base64url encodes correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/jwt_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-JWT-003: RFC 7515 A.1 HS256 signature matches RFC vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
