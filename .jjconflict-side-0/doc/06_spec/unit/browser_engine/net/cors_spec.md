# CORS Specification

> Verifies CorsChecker logic: needs_preflight detection, is_simple_method, preflight OPTIONS construction, and validate_preflight response checking. No network calls — pure logic tests on entity types and checker functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORS Specification

Verifies CorsChecker logic: needs_preflight detection, is_simple_method, preflight OPTIONS construction, and validate_preflight response checking. No network calls — pure logic tests on entity types and checker functions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M16-AC5 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/browser_engine/net/cors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies CorsChecker logic: needs_preflight detection, is_simple_method,
preflight OPTIONS construction, and validate_preflight response checking.
No network calls — pure logic tests on entity types and checker functions.

## Scenarios

### is_simple_method

#### AC-5: GET is a simple method

- AC-5: GET is a simple method
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: GET is a simple method")
val result = is_simple_method("GET")
expect(result).to_equal(true)
```

</details>

#### AC-5: POST is a simple method

- AC-5: POST is a simple method
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: POST is a simple method")
val result = is_simple_method("POST")
expect(result).to_equal(true)
```

</details>

#### AC-5: HEAD is a simple method

- AC-5: HEAD is a simple method
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: HEAD is a simple method")
val result = is_simple_method("HEAD")
expect(result).to_equal(true)
```

</details>

#### AC-5: PUT is not a simple method

- AC-5: PUT is not a simple method
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: PUT is not a simple method")
val result = is_simple_method("PUT")
expect(result).to_equal(false)
```

</details>

#### AC-5: DELETE is not a simple method

- AC-5: DELETE is not a simple method
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: DELETE is not a simple method")
val result = is_simple_method("DELETE")
expect(result).to_equal(false)
```

</details>

#### AC-5: PATCH is not a simple method

- AC-5: PATCH is not a simple method
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: PATCH is not a simple method")
val result = is_simple_method("PATCH")
expect(result).to_equal(false)
```

</details>

### needs_preflight

#### AC-5: cross-origin GET does not need preflight

- AC-5: cross-origin GET does not need preflight
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: cross-origin GET does not need preflight")
val req = make_cors_request("GET", "application/x-www-form-urlencoded")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(false)
```

</details>

#### AC-5: cross-origin PUT needs preflight

- AC-5: cross-origin PUT needs preflight
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: cross-origin PUT needs preflight")
val req = make_cors_request("PUT", "application/json")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

#### AC-5: cross-origin DELETE needs preflight

- AC-5: cross-origin DELETE needs preflight
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: cross-origin DELETE needs preflight")
val req = make_cors_request("DELETE", "")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

#### AC-5: cross-origin POST with application/json needs preflight

- AC-5: cross-origin POST with application/json needs preflight
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: cross-origin POST with application/json needs preflight")
val req = make_cors_request("POST", "application/json")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

#### AC-5: same-origin request does not need preflight

- AC-5: same-origin request does not need preflight
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: same-origin request does not need preflight")
val req = make_cors_request("PUT", "application/json")
val result = needs_preflight(req, make_same_origin())
expect(result).to_equal(false)
```

</details>

#### AC-5: cross-origin PATCH needs preflight

- AC-5: cross-origin PATCH needs preflight
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: cross-origin PATCH needs preflight")
val req = make_cors_request("PATCH", "application/json")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

### create_preflight

#### AC-5: preflight uses OPTIONS method

- AC-5: preflight uses OPTIONS method
   - Expected: pf.method equals `OPTIONS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: preflight uses OPTIONS method")
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.method).to_equal("OPTIONS")
```

</details>

#### AC-5: preflight includes Access-Control-Request-Method

- AC-5: preflight includes Access-Control-Request-Method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: preflight includes Access-Control-Request-Method")
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.headers).to_contain("Access-Control-Request-Method")
```

</details>

#### AC-5: Access-Control-Request-Method value matches original method

- AC-5: Access-Control-Request-Method value matches original method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: Access-Control-Request-Method value matches original method")
val original = make_cors_request("DELETE", "")
val pf = create_preflight(original)
expect(pf.headers).to_contain("DELETE")
```

</details>

#### AC-5: preflight URL matches original URL

- AC-5: preflight URL matches original URL
   - Expected: pf.url.host equals `original.url.host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: preflight URL matches original URL")
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.url.host).to_equal(original.url.host)
```

</details>

### CorsChecker.validate_preflight

#### AC-5: response allowing method returns Allowed

- AC-5: response allowing method returns Allowed
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: response allowing method returns Allowed")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("PUT", "https://app.example.com")
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: response denying method returns Denied

- AC-5: response denying method returns Denied
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: response denying method returns Denied")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("GET", "https://app.example.com")
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: response with wrong origin returns Denied

- AC-5: response with wrong origin returns Denied
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: response with wrong origin returns Denied")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("PUT", "https://other.example.com")
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: response with wildcard origin returns Allowed

- AC-5: response with wildcard origin returns Allowed
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: response with wildcard origin returns Allowed")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_wildcard_preflight_response("PUT")
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: method-specific response allows the requested method

- AC-5: method-specific response allows the requested method
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: method-specific response allows the requested method")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_method(
    make_preflight_response("PUT, PATCH", "https://app.example.com"),
    "PATCH"
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: method-specific response denies an omitted requested method

- AC-5: method-specific response denies an omitted requested method
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: method-specific response denies an omitted requested method")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_method(
    make_preflight_response("PUT", "https://app.example.com"),
    "DELETE"
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: wildcard origin denies credentialed method-specific preflight

- AC-5: wildcard origin denies credentialed method-specific preflight
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: wildcard origin denies credentialed method-specific preflight")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_method_with_credentials(
    make_wildcard_preflight_response("PUT"),
    "PUT",
    "include"
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: credentialed preflight requires explicit credentials grant

- AC-5: credentialed preflight requires explicit credentials grant
   - Expected: denied == PreflightResult.Denied is true
   - Expected: allowed == PreflightResult.Allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: credentialed preflight requires explicit credentials grant")
val checker = make_checker("https://app.example.com")
val denied = checker.validate_preflight_method_with_credentials(
    make_preflight_response("PUT", "https://app.example.com"),
    "PUT",
    "include"
)
expect(denied == PreflightResult.Denied).to_equal(true)
val allowed = checker.validate_preflight_method_with_credentials(
    make_preflight_response(
        "PUT", "https://app.example.com"
    ) + "Access-Control-Allow-Credentials: true\r\n",
    "PUT",
    "include"
)
expect(allowed == PreflightResult.Allowed).to_equal(true)
```

</details>

#### AC-5: header-specific response allows every requested header token

- AC-5: header-specific response allows every requested header token
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: header-specific response allows every requested header token")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_headers(
    make_header_preflight_response("Content-Type, X-Trace-Id", "https://app.example.com"),
    "content-type, x-trace-id"
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: header-specific response denies omitted requested headers

- AC-5: header-specific response denies omitted requested headers
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: header-specific response denies omitted requested headers")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_headers(
    make_header_preflight_response("Content-Type", "https://app.example.com"),
    "content-type, x-trace-id"
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: wildcard allow-headers does not permit authorization

- AC-5: wildcard allow-headers does not permit authorization
- Require an explicit preflight grant for Authorization
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: wildcard allow-headers does not permit authorization")
step("Require an explicit preflight grant for Authorization")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_headers(
    make_header_preflight_response("*", "https://app.example.com"),
    "authorization, x-api-key"
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `d5122b84d362080159e255c6086bf09e9d470f95cef2c6e2dbf34e3f67837cd6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5122b84d362080159e255c6086bf09e9d470f95cef2c6e2dbf34e3f67837cd6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5122b84d362080159e255c6086bf09e9d470f95cef2c6e2dbf34e3f67837cd6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/browser_engine/net/cors_spec.spl
mirror: doc/06_spec/unit/browser_engine/net/cors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/net/cors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/net/cors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/net/cors_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: GET is a simple method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/net/cors_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: POST is a simple method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/net/cors_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: HEAD is a simple method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
