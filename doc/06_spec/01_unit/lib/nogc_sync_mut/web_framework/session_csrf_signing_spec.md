# Session Csrf Signing Specification

> Tests covering web_framework signing paths actually execute.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Csrf Signing Specification

## Scenarios

### web_framework signing paths actually execute

#### POSITIVE CONTROL: compute_signature runs and returns a 64-char hex digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POSITIVE CONTROL: compute_signature runs and returns a 64-char hex digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: compute_signature runs and returns a 64-char hex digest")
# Before the fix this line could not execute: the function body had a
# type error, so any call died with
#   semantic: type mismatch: cannot convert string to int
val sig = compute_signature("user_42|role=admin", "s3cr3t-key")
assert_true(sig != "")
assert_equal(sig.len(), 64)
```

</details>

#### POSITIVE CONTROL: csrf_token_for_session runs and returns a 64-char hex token

- POSITIVE CONTROL: csrf_token_for_session runs and returns a 64-char hex token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POSITIVE CONTROL: csrf_token_for_session runs and returns a 64-char hex token")
val tok = csrf_token_for_session("session_abc", "my-secret")
assert_true(tok != "")
assert_equal(tok.len(), 64)
```

</details>

#### compute_signature matches the openssl HMAC-SHA256 oracle

- compute_signature matches the openssl HMAC-SHA256 oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compute_signature matches the openssl HMAC-SHA256 oracle")
# printf '%s' "user_42|role=admin" | openssl dgst -sha256 -hmac "s3cr3t-key"
assert_equal(
    compute_signature("user_42|role=admin", "s3cr3t-key"),
    "76e6d0e8d2475fc78a88f884145dd586abd43904408523306526b462f6b6934d")
```

</details>

#### csrf_token_for_session matches the openssl HMAC-SHA256 oracle

- csrf_token_for_session matches the openssl HMAC-SHA256 oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("csrf_token_for_session matches the openssl HMAC-SHA256 oracle")
# The token is HMAC over the message "csrf:{session_id}".
# printf '%s' "csrf:session_abc" | openssl dgst -sha256 -hmac "my-secret"
assert_equal(
    csrf_token_for_session("session_abc", "my-secret"),
    "36129a1d3ec8f47c11d9006e31a7d1993f9f094eee4157518092f316461eeff5")
```

</details>

#### output is lowercase hex only

- output is lowercase hex only


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("output is lowercase hex only")
val sig = compute_signature("payload", "key")
val allowed = "0123456789abcdef"
var i = 0
while i < sig.len():
    assert_true(allowed.contains(sig.char_at(i)))
    i = i + 1
```

</details>

#### is deterministic for identical inputs

- is deterministic for identical inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic for identical inputs")
assert_equal(
    compute_signature("same-data", "same-key"),
    compute_signature("same-data", "same-key"))
assert_equal(
    csrf_token_for_session("sid-1", "sec-1"),
    csrf_token_for_session("sid-1", "sec-1"))
```

</details>

#### changes when the SECRET changes (the security property)

- changes when the SECRET changes (the security property)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("changes when the SECRET changes (the security property)")
# If this failed, the secret would not be participating and any caller
# could forge a signature.
assert_true(
    compute_signature("data", "secret-A") != compute_signature("data", "secret-B"))
assert_true(
    csrf_token_for_session("sid", "secret-A") != csrf_token_for_session("sid", "secret-B"))
```

</details>

#### changes when the DATA changes (no collision on a one-char edit)

- changes when the DATA changes (no collision on a one-char edit)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("changes when the DATA changes (no collision on a one-char edit)")
assert_true(
    compute_signature("amount=10", "k") != compute_signature("amount=90", "k"))
```

</details>

#### binds a CSRF token to its session id

- binds a CSRF token to its session id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds a CSRF token to its session id")
# Tokens must not be transplantable between sessions.
assert_true(
    csrf_token_for_session("session_a", "s") != csrf_token_for_session("session_b", "s"))
```

</details>

#### handles empty data and empty session id without failing

- handles empty data and empty session id without failing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty data and empty session id without failing")
assert_equal(compute_signature("", "k").len(), 64)
assert_equal(csrf_token_for_session("", "s").len(), 64)
```

</details>

#### handles UTF-8 multibyte input

- handles UTF-8 multibyte input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles UTF-8 multibyte input")
# Key and data are UTF-8 text; multibyte content must not truncate.
assert_equal(compute_signature("héllo wörld ✓", "kéy").len(), 64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web_framework signing paths actually execute.
- web_framework signing paths actually execute

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEBFW-SIGNING-EXECUTES`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6a788a0b922aa32e7bb311a0ad302e867997c81f6de973e25d762ead8b58c2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6a788a0b922aa32e7bb311a0ad302e867997c81f6de973e25d762ead8b58c2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6a788a0b922aa32e7bb311a0ad302e867997c81f6de973e25d762ead8b58c2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: compute_signature runs and returns a 64-char hex digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: csrf_token_for_session runs and returns a 64-char hex token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compute_signature matches the openssl HMAC-SHA256 oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
