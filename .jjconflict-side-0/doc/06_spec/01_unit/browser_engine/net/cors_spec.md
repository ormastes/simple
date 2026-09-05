# CORS Specification

> Verifies CorsChecker logic: needs_preflight detection, is_simple_method, preflight OPTIONS construction, and validate_preflight response checking. No network calls — pure logic tests on entity types and checker functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

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
| Source | `test/01_unit/browser_engine/net/cors_spec.spl` |
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: cross-origin GET does not need preflight")
val req = make_cors_request("GET", "application/x-www-form-urlencoded")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(false)
```

</details>

#### AC-5: cross-origin GET with a custom header needs preflight

- AC-5: cross-origin GET with a custom header needs preflight
- Classify a non-safelisted author request header
   - Expected: needs_preflight(req, make_other_origin()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: cross-origin GET with a custom header needs preflight")
step("Classify a non-safelisted author request header")
var req = make_cors_request("GET", "")
req.headers = "X-Admin-Action: delete"
expect(needs_preflight(req, make_other_origin())).to_equal(true)
```

</details>

#### AC-5: aggregate safelisted values cross at 1025 bytes

- AC-5: aggregate safelisted values cross at 1025 bytes
- Exercise the aggregate safelisted value boundary
   - Expected: needs_preflight(req, make_other_origin()) is false
   - Expected: cors_unsafe_request_header_names(req.headers) equals ``
   - Expected: needs_preflight(req, make_other_origin()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: aggregate safelisted values cross at 1025 bytes")
step("Exercise the aggregate safelisted value boundary")
val value = "a".repeat(128)
var at_limit = ""
var index = 0
while index < 8:
    at_limit = at_limit + "Accept: {value}\r\n"
    index = index + 1
var req = make_cors_request("GET", "")
req.headers = at_limit
expect(needs_preflight(req, make_other_origin())).to_equal(false)
expect(cors_unsafe_request_header_names(req.headers)).to_equal("")

req.headers = at_limit + "Content-Language: e\r\n"
expect(needs_preflight(req, make_other_origin())).to_equal(true)
expect(cors_unsafe_request_header_names(req.headers)).to_equal(
    "accept, content-language"
)
```

</details>

#### AC-5: safelist limits count UTF-8 bytes

- AC-5: safelist limits count UTF-8 bytes
- Hold a multibyte Accept value at the 128-byte boundary
- Count multibyte values toward the 1024-byte aggregate
   - Expected: cors_unsafe_request_header_names(aggregate) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: safelist limits count UTF-8 bytes")
step("Hold a multibyte Accept value at the 128-byte boundary")
val two_byte = "é"
val at_limit = two_byte.repeat(64)
val over_limit = two_byte.repeat(65)
expect(cors_unsafe_request_header_names(
    "Accept: {at_limit}\r\n"
)).to_equal("")
expect(cors_unsafe_request_header_names(
    "Accept: {over_limit}\r\n"
)).to_equal("accept")

step("Count multibyte values toward the 1024-byte aggregate")
var aggregate = ""
var index = 0
while index < 8:
    aggregate = aggregate + "Accept: {at_limit}\r\n"
    index = index + 1
expect(cors_unsafe_request_header_names(aggregate)).to_equal("")
expect(cors_unsafe_request_header_names(
    aggregate + "Content-Language: e\r\n"
)).to_equal("accept, content-language")
```

</details>

#### AC-5: aggregate escalation includes a safelisted Range

- AC-5: aggregate escalation includes a safelisted Range
- Exercise Range on both sides of the aggregate boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: aggregate escalation includes a safelisted Range")
step("Exercise Range on both sides of the aggregate boundary")
val accept_value = "a".repeat(127)
var headers = ""
var index = 0
while index < 8:
    headers = headers + "Accept: {accept_value}\r\n"
    index = index + 1
expect(cors_unsafe_request_header_names(
    headers + "Range: bytes=0-\r\n"
)).to_equal("")
expect(cors_unsafe_request_header_names(
    headers + "Range: bytes=0-0\r\n"
)).to_equal("accept, range")
```

</details>

#### AC-5: Range safelist accepts only ordered single ranges

- AC-5: Range safelist accepts only ordered single ranges
- Accept an open range and reject reversed, suffix, and multiple ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: Range safelist accepts only ordered single ranges")
step("Accept an open range and reject reversed, suffix, and multiple ranges")
expect(cors_unsafe_request_header_names(
    "Range: bytes=0-\r\n"
)).to_equal("")
expect(cors_unsafe_request_header_names(
    "Range: bytes=5-5\r\n"
)).to_equal("")
expect(cors_unsafe_request_header_names(
    "Range: bytes=5-4\r\n"
)).to_equal("range")
expect(cors_unsafe_request_header_names(
    "Range: bytes=-5\r\n"
)).to_equal("range")
expect(cors_unsafe_request_header_names(
    "Range: bytes=0-1, 4-5\r\n"
)).to_equal("range")
```

</details>

#### AC-5: duplicate Range lines combine before safelist validation

- AC-5: duplicate Range lines combine before safelist validation
- Reject two individually valid Range lines as a multiple range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: duplicate Range lines combine before safelist validation")
step("Reject two individually valid Range lines as a multiple range")
expect(cors_unsafe_request_header_names(
    "Range: bytes=0-\r\nRange: bytes=1-2\r\n"
)).to_equal("range")
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: preflight includes Access-Control-Request-Method")
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.headers).to_contain("Access-Control-Request-Method")
```

</details>

#### AC-5: preflight emits exact sorted unsafe author header names

- AC-5: preflight emits exact sorted unsafe author header names
- Build OPTIONS metadata from author request headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: preflight emits exact sorted unsafe author header names")
step("Build OPTIONS metadata from author request headers")
var original = make_cors_request("GET", "")
original.headers = (
    "X-Admin-Action: delete\r\n" +
    "Authorization: Bearer secret\r\n" +
    "Accept: text/plain\r\n" +
    "Origin: https://app.example.com\r\n"
)
val preflight = create_preflight(original)
expect(preflight.headers).to_contain(
    "Access-Control-Request-Headers: " +
    "authorization, x-admin-action\r\n"
)
expect(preflight.headers.contains(
    "Access-Control-Request-Headers: accept"
)).to_equal(false)
```

</details>

#### AC-5: Access-Control-Request-Method value matches original method

- AC-5: Access-Control-Request-Method value matches original method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: response with wrong origin returns Denied")
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("PUT", "https://other.example.com")
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: duplicate allow-origin headers fail closed in either order

- AC-5: duplicate allow-origin headers fail closed in either order


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: duplicate allow-origin headers fail closed in either order")
val checker = make_checker("https://app.example.com")
val variants = [
    "Access-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Origin: https://attacker.example\r\nAccess-Control-Allow-Methods: PUT\r\n",
    "Access-Control-Allow-Origin: https://attacker.example\r\nAccess-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Methods: PUT\r\n",
    "Access-Control-Allow-Origin:\r\nAccess-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Methods: PUT\r\n",
    "Access-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Origin:\r\nAccess-Control-Allow-Methods: PUT\r\n"
]
for headers in variants:
    expect(
        checker.validate_preflight(headers) == PreflightResult.Denied
    ).to_equal(true)
    expect(checker.can_read_body(
        make_target_url(), headers, "omit"
    )).to_equal(false)
```

</details>

#### AC-5: repeated list-valued CORS headers remain combined

- AC-5: repeated list-valued CORS headers remain combined
- Combine repeated grants without widening Authorization


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: repeated list-valued CORS headers remain combined")
step("Combine repeated grants without widening Authorization")
val checker = make_checker("https://app.example.com")
val methods = "Access-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Methods: PATCH\r\nAccess-Control-Allow-Methods: PUT\r\n"
val headers = "Access-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Headers: Content-Type\r\nAccess-Control-Allow-Headers: X-Trace-Id\r\n"
val wildcard_headers = "Access-Control-Allow-Origin: https://app.example.com\r\nAccess-Control-Allow-Headers: *\r\nAccess-Control-Allow-Headers: *\r\n"

expect(
    checker.validate_preflight_method(
        methods, "PUT"
    ) == PreflightResult.Allowed
).to_equal(true)
expect(checker.validate_preflight_headers(
    headers, "content-type, x-trace-id"
) == PreflightResult.Allowed).to_equal(true)
expect(checker.validate_preflight_headers(
    wildcard_headers, "authorization"
) == PreflightResult.Denied).to_equal(true)
```

</details>

#### AC-5: an unset requester origin fails closed

- AC-5: an unset requester origin fails closed
   - Expected: result == PreflightResult.Denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: an unset requester origin fails closed")
val checker = make_checker("")
val result = checker.validate_preflight(
    make_preflight_response("PUT", "https://attacker.example")
)
expect(result == PreflightResult.Denied).to_equal(true)
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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

#### AC-5: safelisted method needs no allow-methods token

- AC-5: safelisted method needs no allow-methods token
- Validate a header-triggered GET preflight without ACAM


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: safelisted method needs no allow-methods token")
step("Validate a header-triggered GET preflight without ACAM")
val checker = make_checker("https://app.example.com")
val response = (
    "Access-Control-Allow-Origin: https://app.example.com\r\n"
)
expect(checker.validate_preflight_method_with_credentials(
    response, "GET", "omit"
) == PreflightResult.Allowed).to_equal(true)
```

</details>

#### AC-5: allow-methods wildcard depends on credentials mode

- AC-5: allow-methods wildcard depends on credentials mode
- Apply ACAM wildcard to non-simple method credentials


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: allow-methods wildcard depends on credentials mode")
step("Apply ACAM wildcard to non-simple method credentials")
val checker = make_checker("https://app.example.com")
val response = (
    "Access-Control-Allow-Origin: https://app.example.com\r\n" +
    "Access-Control-Allow-Methods: *\r\n"
)
expect(checker.validate_preflight_method_with_credentials(
    response, "PUT", "omit"
) == PreflightResult.Allowed).to_equal(true)
expect(checker.validate_preflight_method_with_credentials(
    response + "Access-Control-Allow-Credentials: true\r\n",
    "PUT", "include"
) == PreflightResult.Denied).to_equal(true)
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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
# @req REQ-SSPEC-BROWSER_ENGINE
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

#### AC-5: wildcard allow-headers requires explicit Authorization

- AC-5: wildcard allow-headers requires explicit Authorization
- Distinguish ordinary custom headers from Authorization


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: wildcard allow-headers requires explicit Authorization")
step("Distinguish ordinary custom headers from Authorization")
val checker = make_checker("https://app.example.com")
val wildcard = make_header_preflight_response(
    "*", "https://app.example.com"
)
expect(checker.validate_preflight_headers(
    wildcard, "x-api-key"
) == PreflightResult.Allowed).to_equal(true)
expect(checker.validate_preflight_headers(
    wildcard,
    "authorization, x-api-key"
) == PreflightResult.Denied).to_equal(true)
expect(checker.validate_preflight_headers(
    make_header_preflight_response(
        "Authorization, X-Api-Key", "https://app.example.com"
    ),
    "authorization, x-api-key"
) == PreflightResult.Allowed).to_equal(true)
```

</details>

#### AC-5: credentialed allow-headers wildcard is literal

- AC-5: credentialed allow-headers wildcard is literal
- Require explicit custom header grants with credentials


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: credentialed allow-headers wildcard is literal")
step("Require explicit custom header grants with credentials")
val checker = make_checker("https://app.example.com")
val response = (
    "Access-Control-Allow-Origin: https://app.example.com\r\n" +
    "Access-Control-Allow-Credentials: true\r\n" +
    "Access-Control-Allow-Headers: *\r\n"
)
expect(checker.validate_preflight_headers_with_credentials(
    response, "x-api-key", "include"
) == PreflightResult.Denied).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89e3c44903535e3da41bebd03c24f8f20514582607a6ffbc137b713286c3a432`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89e3c44903535e3da41bebd03c24f8f20514582607a6ffbc137b713286c3a432`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89e3c44903535e3da41bebd03c24f8f20514582607a6ffbc137b713286c3a432`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/browser_engine/net/cors_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/net/cors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/net/cors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/net/cors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/net/cors_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: GET is a simple method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/net/cors_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: POST is a simple method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/net/cors_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: HEAD is a simple method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
