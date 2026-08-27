# Jwt Rfc7519 Kat Specification

> Tests covering JWT HS256 — RFC 7515 Appendix A.1 KAT, JWT HS256 — tamper rejection, JWT EdDSA — RFC 8037 round-trip, JWT security — alg=none unconditional rejection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jwt Rfc7519 Kat Specification

## Scenarios

### JWT HS256 — RFC 7515 Appendix A.1 KAT

#### sign produces exact RFC 7515 A.1 compact JWT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sign produces exact RFC 7515 A.1 compact JWT
   - Expected: _u8_to_text(jwt) equals `_hs256_expected_compact()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sign produces exact RFC 7515 A.1 compact JWT")
val jwt = jwt_sign_hs256(_hs256_header(), _hs256_payload(), _hs256_key())
expect(_u8_to_text(jwt)).to_equal(_hs256_expected_compact())
```

</details>

#### verify accepts the RFC 7515 A.1 compact JWT

- verify accepts the RFC 7515 A.1 compact JWT
   - Expected: _hs256_verify_ok(jwt, _hs256_key()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify accepts the RFC 7515 A.1 compact JWT")
val jwt = _text_to_u8(_hs256_expected_compact())
expect(_hs256_verify_ok(jwt, _hs256_key())).to_equal(true)
```

</details>

### JWT HS256 — tamper rejection

#### tampered payload is rejected

- tampered payload is rejected
   - Expected: _hs256_verify_err(jwt, _hs256_key()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered payload is rejected")
# Flip one character in the payload segment
val good = _hs256_expected_compact()
# Replace first char after first dot with 'X'
val dot1 = good.index_of(".")
val tampered = good.substring(0, dot1 + 1) + "X" + good.substring(dot1 + 2, good.length())
val jwt = _text_to_u8(tampered)
expect(_hs256_verify_err(jwt, _hs256_key())).to_equal(true)
```

</details>

#### tampered signature is rejected

- tampered signature is rejected
   - Expected: _hs256_verify_err(jwt, _hs256_key()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tampered signature is rejected")
# Flip one character in the signature segment (last segment)
val good = _hs256_expected_compact()
val last_dot = good.last_index_of(".")
val tampered = good.substring(0, last_dot + 1) + "X" + good.substring(last_dot + 2, good.length())
val jwt = _text_to_u8(tampered)
expect(_hs256_verify_err(jwt, _hs256_key())).to_equal(true)
```

</details>

### JWT EdDSA — RFC 8037 round-trip

#### EdDSA sign then verify round-trip succeeds

- EdDSA sign then verify round-trip succeeds
   - Expected: _eddsa_verify_ok(jwt, _eddsa_pubkey()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EdDSA sign then verify round-trip succeeds")
val jwt = jwt_sign_eddsa(_eddsa_header(), _eddsa_payload(), _eddsa_seed())
expect(_eddsa_verify_ok(jwt, _eddsa_pubkey())).to_equal(true)
```

</details>

#### EdDSA decoded payload matches original

- EdDSA decoded payload matches original


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EdDSA decoded payload matches original")
val jwt = jwt_sign_eddsa(_eddsa_header(), _eddsa_payload(), _eddsa_seed())
val payload = _eddsa_verify_payload(jwt, _eddsa_pubkey())
expect(_u8_to_text(payload)).to_equal(
    "{\"iss\":\"joe\",\"exp\":1300819380,\"http://example.com/is_root\":true}"
)
```

</details>

### JWT security — alg=none unconditional rejection

#### jwt_verify_hs256 rejects alg=none token

- jwt_verify_hs256 rejects alg=none token
   - Expected: _hs256_verify_err(jwt, _hs256_key()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jwt_verify_hs256 rejects alg=none token")
val jwt = _alg_none_header_b64_jwt()
expect(_hs256_verify_err(jwt, _hs256_key())).to_equal(true)
```

</details>

#### jwt_verify_eddsa rejects alg=none token

- jwt_verify_eddsa rejects alg=none token
   - Expected: _eddsa_verify_err(jwt, _eddsa_pubkey()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jwt_verify_eddsa rejects alg=none token")
val jwt = _alg_none_header_b64_jwt()
expect(_eddsa_verify_err(jwt, _eddsa_pubkey())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/jwt_rfc7519_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JWT HS256 — RFC 7515 Appendix A.1 KAT, JWT HS256 — tamper rejection, JWT EdDSA — RFC 8037 round-trip, JWT security — alg=none unconditional rejection.
- JWT HS256 — RFC 7515 Appendix A.1 KAT
- JWT HS256 — tamper rejection
- JWT EdDSA — RFC 8037 round-trip
- JWT security — alg=none unconditional rejection

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `41c90b2cc7cf65de720f9be8cab181a25df33bff945e95ca573d76bbfb4329d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `41c90b2cc7cf65de720f9be8cab181a25df33bff945e95ca573d76bbfb4329d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `41c90b2cc7cf65de720f9be8cab181a25df33bff945e95ca573d76bbfb4329d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/jwt_rfc7519_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/jwt_rfc7519_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/jwt_rfc7519_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/jwt_rfc7519_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/jwt_rfc7519_kat_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sign produces exact RFC 7515 A.1 compact JWT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/jwt_rfc7519_kat_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verify accepts the RFC 7515 A.1 compact JWT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/jwt_rfc7519_kat_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tampered payload is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
