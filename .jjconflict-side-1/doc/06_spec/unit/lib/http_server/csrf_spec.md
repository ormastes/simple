# Csrf Specification

> Tests covering CSRF token generation fail-closed guard, CSRF constant-time token comparison, CsrfConfig defaults, CSRF header and cookie extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Csrf Specification

## Scenarios

### CSRF token generation fail-closed guard

#### returns empty string when secret_key is empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns empty string when secret_key is empty
   - Expected: token equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string when secret_key is empty")
val config = CsrfConfig.default()
val token = generate_csrf_token(config, "session-abc")
expect(token).to_equal("")
```

</details>

### CSRF constant-time token comparison

#### accepts identical tokens

- accepts identical tokens
   - Expected: constant_time_eq(token, token) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts identical tokens")
val token = "abc123def456ghi789jkl012mno345pq"
expect(constant_time_eq(token, token)).to_equal(true)
```

</details>

#### rejects mismatched tokens

- rejects mismatched tokens
   - Expected: constant_time_eq(token_a, token_b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects mismatched tokens")
val token_a = "abc123def456ghi789jkl012mno345pq"
val token_b = "zzz999yyy888xxx777www666vvv555uu"
expect(constant_time_eq(token_a, token_b)).to_equal(false)
```

</details>

#### rejects an empty token against a valid token

- rejects an empty token against a valid token
   - Expected: constant_time_eq("", token) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty token against a valid token")
val token = "abc123def456ghi789jkl012mno345pq"
expect(constant_time_eq("", token)).to_equal(false)
```

</details>

### CsrfConfig defaults

#### ships with no secret key so generation stays fail-closed

- ships with no secret key so generation stays fail-closed
   - Expected: CsrfConfig.default().secret_key equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ships with no secret key so generation stays fail-closed")
expect(CsrfConfig.default().secret_key).to_equal("")
```

</details>

#### exempts GET

- exempts GET
   - Expected: CsrfConfig.default().exempt_methods contains `GET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exempts GET")
expect(CsrfConfig.default().exempt_methods.contains("GET")).to_equal(true)
```

</details>

#### exempts HEAD

- exempts HEAD
   - Expected: CsrfConfig.default().exempt_methods contains `HEAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exempts HEAD")
expect(CsrfConfig.default().exempt_methods.contains("HEAD")).to_equal(true)
```

</details>

#### exempts OPTIONS

- exempts OPTIONS
   - Expected: CsrfConfig.default().exempt_methods contains `OPTIONS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exempts OPTIONS")
expect(CsrfConfig.default().exempt_methods.contains("OPTIONS")).to_equal(true)
```

</details>

#### does not exempt POST

- does not exempt POST
   - Expected: CsrfConfig.default().exempt_methods does not contain `POST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not exempt POST")
expect(CsrfConfig.default().exempt_methods.contains("POST")).to_equal(false)
```

</details>

#### does not exempt DELETE

- does not exempt DELETE
   - Expected: CsrfConfig.default().exempt_methods does not contain `DELETE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not exempt DELETE")
expect(CsrfConfig.default().exempt_methods.contains("DELETE")).to_equal(false)
```

</details>

### CSRF header and cookie extraction

#### finds the token header case-insensitively

- finds the token header case-insensitively
   - Expected: get_header_value([("X-CSRF-Token", "mytoken123")], "x-csrf-token") equals `mytoken123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds the token header case-insensitively")
expect(get_header_value([("X-CSRF-Token", "mytoken123")], "x-csrf-token")).to_equal("mytoken123")
```

</details>

#### extracts the named cookie from a multi-cookie header

- extracts the named cookie from a multi-cookie header
   - Expected: get_cookie_value([("Cookie", "session=abc; csrf_token=tok456")], "csrf_token") equals `tok456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the named cookie from a multi-cookie header")
expect(get_cookie_value([("Cookie", "session=abc; csrf_token=tok456")], "csrf_token")).to_equal("tok456")
```

</details>

#### returns empty when no Cookie header is present

- returns empty when no Cookie header is present
   - Expected: get_cookie_value([("Content-Type", "application/json")], "csrf_token") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when no Cookie header is present")
expect(get_cookie_value([("Content-Type", "application/json")], "csrf_token")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/http_server/csrf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSRF token generation fail-closed guard, CSRF constant-time token comparison, CsrfConfig defaults, CSRF header and cookie extraction.
- CSRF token generation fail-closed guard
- CSRF constant-time token comparison
- CsrfConfig defaults
- CSRF header and cookie extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `8dcf90705e29e6641987b189d6916aded6070636cf2d128895fea2d21ecf482f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8dcf90705e29e6641987b189d6916aded6070636cf2d128895fea2d21ecf482f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8dcf90705e29e6641987b189d6916aded6070636cf2d128895fea2d21ecf482f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/http_server/csrf_spec.spl
mirror: doc/06_spec/unit/lib/http_server/csrf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/http_server/csrf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/http_server/csrf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/http_server/csrf_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string when secret_key is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/http_server/csrf_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts identical tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/http_server/csrf_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects mismatched tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
