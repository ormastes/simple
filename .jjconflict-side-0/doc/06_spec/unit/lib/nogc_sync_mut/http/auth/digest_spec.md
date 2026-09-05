# Digest Specification

> Tests covering RFC 7616 Digest SHA-256 — §3.9.1 KAT, RFC 7616 Digest MD5 — §3.9.1 KAT, RFC 7616 Digest verify — accept correct credentials, RFC 7616 Digest verify — tamper-reject wrong password, RFC 7616 Digest challenge format, RFC 7616 Digest SHA-512-256.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Digest Specification

## Scenarios

### RFC 7616 Digest SHA-256 — §3.9.1 KAT

#### response hex matches RFC 7616 §3.9.1 exact value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- response hex matches RFC 7616 §3.9.1 exact value
   - Expected: full_header contains `expected_fragment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("response hex matches RFC 7616 §3.9.1 exact value")
val full_header = http_digest_make_response(_rfc7616_sha256_params())
# The response= field must contain the exact 64-hex-char value from RFC
val expected_fragment = "response=\"753927fa0e85d155564e2e272a28d1802ca10daf4496794697cf8db5856cb6c1\""
expect(full_header.contains(expected_fragment)).to_equal(true)
```

</details>

#### Authorization header includes correct username

- Authorization header includes correct username
   - Expected: full_header contains `username="Mufasa"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Authorization header includes correct username")
val full_header = http_digest_make_response(_rfc7616_sha256_params())
expect(full_header.contains("username=\"Mufasa\"")).to_equal(true)
```

</details>

#### Authorization header includes correct realm

- Authorization header includes correct realm
   - Expected: full_header contains `realm="http-auth@example.org"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Authorization header includes correct realm")
val full_header = http_digest_make_response(_rfc7616_sha256_params())
expect(full_header.contains("realm=\"http-auth@example.org\"")).to_equal(true)
```

</details>

#### Authorization header includes algorithm=SHA-256

- Authorization header includes algorithm=SHA-256
   - Expected: full_header contains `algorithm=SHA-256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Authorization header includes algorithm=SHA-256")
val full_header = http_digest_make_response(_rfc7616_sha256_params())
expect(full_header.contains("algorithm=SHA-256")).to_equal(true)
```

</details>

### RFC 7616 Digest MD5 — §3.9.1 KAT

#### response hex matches RFC 7616 §3.9.1 MD5 exact value

- response hex matches RFC 7616 §3.9.1 MD5 exact value
   - Expected: full_header contains `expected_fragment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("response hex matches RFC 7616 §3.9.1 MD5 exact value")
val full_header = http_digest_make_response(_rfc7616_md5_params())
val expected_fragment = "response=\"8ca523f5e9506fed4657c9700eebdbec\""
expect(full_header.contains(expected_fragment)).to_equal(true)
```

</details>

#### Authorization header includes algorithm=MD5

- Authorization header includes algorithm=MD5
   - Expected: full_header contains `algorithm=MD5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Authorization header includes algorithm=MD5")
val full_header = http_digest_make_response(_rfc7616_md5_params())
expect(full_header.contains("algorithm=MD5")).to_equal(true)
```

</details>

### RFC 7616 Digest verify — accept correct credentials

#### verify accepts correct password for SHA-256

- verify accepts correct password for SHA-256
   - Expected: http_digest_verify(_rfc7616_sha256_verify_params(), "Circle of Life") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify accepts correct password for SHA-256")
expect(http_digest_verify(_rfc7616_sha256_verify_params(), "Circle of Life")).to_equal(true)
```

</details>

#### verify accepts correct password for MD5

- verify accepts correct password for MD5
   - Expected: http_digest_verify(_rfc7616_md5_verify_params(), "Circle of Life") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify accepts correct password for MD5")
expect(http_digest_verify(_rfc7616_md5_verify_params(), "Circle of Life")).to_equal(true)
```

</details>

### RFC 7616 Digest verify — tamper-reject wrong password

#### rejects wrong password for SHA-256

- rejects wrong password for SHA-256
   - Expected: not http_digest_verify(_rfc7616_sha256_verify_params(), "wrong password") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong password for SHA-256")
expect(not http_digest_verify(_rfc7616_sha256_verify_params(), "wrong password")).to_equal(true)
```

</details>

#### rejects wrong password for MD5

- rejects wrong password for MD5
   - Expected: not http_digest_verify(_rfc7616_md5_verify_params(), "wrong password") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong password for MD5")
expect(not http_digest_verify(_rfc7616_md5_verify_params(), "wrong password")).to_equal(true)
```

</details>

#### rejects empty password for SHA-256

- rejects empty password for SHA-256
   - Expected: not http_digest_verify(_rfc7616_sha256_verify_params(), "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty password for SHA-256")
expect(not http_digest_verify(_rfc7616_sha256_verify_params(), "")).to_equal(true)
```

</details>

### RFC 7616 Digest challenge format

#### challenge includes Digest realm and nonce

- challenge includes Digest realm and nonce
   - Expected: challenge.starts_with("Digest ") is true
   - Expected: challenge contains `realm="http-auth@example.org"`
   - Expected: challenge contains `nonce="7ypf/xlj9XXwfDPEoM4URrv/xwf94BcCAzFZH4GiTo0v"`
   - Expected: challenge contains `algorithm=SHA-256`
   - Expected: challenge contains `qop="auth"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("challenge includes Digest realm and nonce")
val challenge = http_digest_make_challenge(
    "http-auth@example.org",
    "7ypf/xlj9XXwfDPEoM4URrv/xwf94BcCAzFZH4GiTo0v",
    "SHA-256",
    "auth"
)
expect(challenge.starts_with("Digest ")).to_equal(true)
expect(challenge.contains("realm=\"http-auth@example.org\"")).to_equal(true)
expect(challenge.contains("nonce=\"7ypf/xlj9XXwfDPEoM4URrv/xwf94BcCAzFZH4GiTo0v\"")).to_equal(true)
expect(challenge.contains("algorithm=SHA-256")).to_equal(true)
expect(challenge.contains("qop=\"auth\"")).to_equal(true)
```

</details>

#### challenge without qop omits qop field

- challenge without qop omits qop field
   - Expected: not challenge contains `qop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("challenge without qop omits qop field")
val challenge = http_digest_make_challenge("realm", "nonce123", "SHA-256", "")
expect(not challenge.contains("qop")).to_equal(true)
```

</details>

### RFC 7616 Digest SHA-512-256

#### make_response returns correct Digest header for SHA-512-256

- make_response returns correct Digest header for SHA-512-256
   - Expected: result.starts_with("Digest ") is true
   - Expected: result contains `algorithm=SHA-512-256`
   - Expected: result contains `response=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("make_response returns correct Digest header for SHA-512-256")
val params = (
    "user", "realm", "password",
    "SHA-512-256",
    "GET", "/path",
    "nonce1", "00000001", "cnonce1", "auth"
)
val result = http_digest_make_response(params)
expect(result.starts_with("Digest ")).to_equal(true)
expect(result.contains("algorithm=SHA-512-256")).to_equal(true)
expect(result.contains("response=")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_sync_mut/http/auth/digest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RFC 7616 Digest SHA-256 — §3.9.1 KAT, RFC 7616 Digest MD5 — §3.9.1 KAT, RFC 7616 Digest verify — accept correct credentials, RFC 7616 Digest verify — tamper-reject wrong password, RFC 7616 Digest challenge format, RFC 7616 Digest SHA-512-256.
- RFC 7616 Digest SHA-256 — §3.9.1 KAT
- RFC 7616 Digest MD5 — §3.9.1 KAT
- RFC 7616 Digest verify — accept correct credentials
- RFC 7616 Digest verify — tamper-reject wrong password
- RFC 7616 Digest challenge format
- RFC 7616 Digest SHA-512-256

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `871b3751ea36ae7c18e84bc1b5567e8dfe0fb357d67fd037b3721c3d40c83874`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `871b3751ea36ae7c18e84bc1b5567e8dfe0fb357d67fd037b3721c3d40c83874`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `871b3751ea36ae7c18e84bc1b5567e8dfe0fb357d67fd037b3721c3d40c83874`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_sync_mut/http/auth/digest_spec.spl
mirror: doc/06_spec/unit/lib/nogc_sync_mut/http/auth/digest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_sync_mut/http/auth/digest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_sync_mut/http/auth/digest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_sync_mut/http/auth/digest_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'response hex matches RFC 7616 §3.9.1 exact value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/http/auth/digest_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Authorization header includes correct username' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/http/auth/digest_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Authorization header includes correct realm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
