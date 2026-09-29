# Auth Token Strict Base64url Specification

> Tests covering JWT/reset-token decode rejects malformed base64url segments, password reset token rejects malformed base64url payload.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auth Token Strict Base64url Specification

## Scenarios

### JWT/reset-token decode rejects malformed base64url segments

#### POSITIVE CONTROL: module under test loaded and a VALID token verifies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POSITIVE CONTROL: module under test loaded and a VALID token verifies


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: module under test loaded and a VALID token verifies")
# Fails RED on a missing/wrong import: demands a SUCCESSFUL auth with
# an exact subject, which no absent or sentinel value can produce.
val h = base64url_encode("{\"alg\":\"HS256\",\"typ\":\"JWT\"}")
val p = base64url_encode("{\"sub\":\"alice\"}")
val r = verify_and_decode_jwt(signed(h, p), cfg())
assert_equal(r.is_ok(), true)
assert_equal(r.unwrap().user_id, "alice")
```

</details>

#### REPRODUCING: malformed PAYLOAD segment is rejected, not decoded lenient

- REPRODUCING: malformed PAYLOAD segment is rejected, not decoded lenient


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REPRODUCING: malformed PAYLOAD segment is rejected, not decoded lenient")
val h = base64url_encode("{\"alg\":\"HS256\",\"typ\":\"JWT\"}")
# 'ab*d{"sub":"alice"}'-ish: an out-of-alphabet '*' inside the payload.
val p = base64url_encode("{\"sub\":\"alice\"}") + "*Zm9v"
assert_equal(verify_and_decode_jwt(signed(h, p), cfg()).is_ok(), false)
```

</details>

#### REPRODUCING: malformed HEADER segment is rejected

- REPRODUCING: malformed HEADER segment is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REPRODUCING: malformed HEADER segment is rejected")
val h = base64url_encode("{\"alg\":\"HS256\"}") + "!!!!"
val p = base64url_encode("{\"sub\":\"alice\"}")
assert_equal(verify_and_decode_jwt(signed(h, p), cfg()).is_ok(), false)
```

</details>

#### DEFECT CLASS: invalid char at first/middle/last offset of payload

- DEFECT CLASS: invalid char at first/middle/last offset of payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: invalid char at first/middle/last offset of payload")
val h = base64url_encode("{\"alg\":\"HS256\"}")
val good = base64url_encode("{\"sub\":\"alice\"}")
val bad_first = "*" + good[1:]
val bad_mid = good[0:4] + "*" + good[5:]
val bad_last = good[0:good.len() - 1] + "*"
for p in [bad_first, bad_mid, bad_last]:
    assert_equal(verify_and_decode_jwt(signed(h, p), cfg()).is_ok(), false)
```

</details>

#### DEFECT CLASS: standard-alphabet '+' and '/' in a segment are rejected

- DEFECT CLASS: standard-alphabet '+' and '/' in a segment are rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: standard-alphabet '+' and '/' in a segment are rejected")
val h = base64url_encode("{\"alg\":\"HS256\"}")
val good = base64url_encode("{\"sub\":\"alice\"}")
for p in [good + "a+bc", good + "ab/c"]:
    assert_equal(verify_and_decode_jwt(signed(h, p), cfg()).is_ok(), false)
```

</details>

#### DEFECT CLASS: segment length 1 mod 4 is rejected

- DEFECT CLASS: segment length 1 mod 4 is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: segment length 1 mod 4 is rejected")
val h = base64url_encode("{\"alg\":\"HS256\"}")
# 5 chars -> residue 1: no byte sequence encodes to such a length.
assert_equal(verify_and_decode_jwt(signed(h, "QWJjZ"), cfg()).is_ok(), false)
```

</details>

### password reset token rejects malformed base64url payload

#### POSITIVE CONTROL: a generated token still verifies

- POSITIVE CONTROL: a generated token still verifies


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: a generated token still verifies")
val svc = PasswordResetService.new("reset-key", 3600)
val tok = svc.generate_token("bob")
assert_equal(tok.is_ok(), true)
val v = svc.verify_token(tok.unwrap())
assert_equal(v.is_ok(), true)
assert_equal(v.unwrap().user_id, "bob")
```

</details>

#### REPRODUCING: malformed payload segment is rejected

- REPRODUCING: malformed payload segment is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REPRODUCING: malformed payload segment is rejected")
val svc = PasswordResetService.new("reset-key", 3600)
val tok = svc.generate_token("bob").unwrap()
val dot = tok.index_of(".")
val payload = tok[0:dot]
# Corrupt the payload with an out-of-alphabet byte. Re-signing is not
# needed: the token must be rejected for BEING malformed, and the
# assertion below only demands rejection.
val bad = payload[0:4] + "*" + payload[5:] + "." + tok[dot + 1:]
assert_equal(svc.verify_token(bad).is_ok(), false)
```

</details>

#### DEFECT CLASS: residue-1 payload length is rejected

- DEFECT CLASS: residue-1 payload length is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DEFECT CLASS: residue-1 payload length is rejected")
val svc = PasswordResetService.new("reset-key", 3600)
assert_equal(svc.verify_token("QWJjZ.sig").is_ok(), false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JWT/reset-token decode rejects malformed base64url segments, password reset token rejects malformed base64url payload.
- JWT/reset-token decode rejects malformed base64url segments
- password reset token rejects malformed base64url payload

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-BASE64URL`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d0bd156dc47263afd8e2a8697ec2396235c1a72c5bf06aeb8f414b7b2ae946ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0bd156dc47263afd8e2a8697ec2396235c1a72c5bf06aeb8f414b7b2ae946ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0bd156dc47263afd8e2a8697ec2396235c1a72c5bf06aeb8f414b7b2ae946ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: module under test loaded and a VALID token verifies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPRODUCING: malformed PAYLOAD segment is rejected, not decoded lenient' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_framework/auth_token_strict_base64url_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPRODUCING: malformed HEADER segment is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
