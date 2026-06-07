# CORS Specification

> Verifies CorsChecker logic: needs_preflight detection, is_simple_method, preflight OPTIONS construction, and validate_preflight response checking. No network calls — pure logic tests on entity types and checker functions.

<!-- sdn-diagram:id=cors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/browser_engine/net/cors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies CorsChecker logic: needs_preflight detection, is_simple_method,
preflight OPTIONS construction, and validate_preflight response checking.
No network calls — pure logic tests on entity types and checker functions.

## Scenarios

### is_simple_method

#### AC-5: GET is a simple method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_simple_method("GET")
expect(result).to_equal(true)
```

</details>

#### AC-5: POST is a simple method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_simple_method("POST")
expect(result).to_equal(true)
```

</details>

#### AC-5: HEAD is a simple method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_simple_method("HEAD")
expect(result).to_equal(true)
```

</details>

#### AC-5: PUT is not a simple method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_simple_method("PUT")
expect(result).to_equal(false)
```

</details>

#### AC-5: DELETE is not a simple method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_simple_method("DELETE")
expect(result).to_equal(false)
```

</details>

#### AC-5: PATCH is not a simple method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_simple_method("PATCH")
expect(result).to_equal(false)
```

</details>

### needs_preflight

#### AC-5: cross-origin GET does not need preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_cors_request("GET", "application/x-www-form-urlencoded")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(false)
```

</details>

#### AC-5: cross-origin PUT needs preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_cors_request("PUT", "application/json")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

#### AC-5: cross-origin DELETE needs preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_cors_request("DELETE", "")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

#### AC-5: cross-origin POST with application/json needs preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_cors_request("POST", "application/json")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

#### AC-5: same-origin request does not need preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_cors_request("PUT", "application/json")
val result = needs_preflight(req, make_same_origin())
expect(result).to_equal(false)
```

</details>

#### AC-5: cross-origin PATCH needs preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_cors_request("PATCH", "application/json")
val result = needs_preflight(req, make_other_origin())
expect(result).to_equal(true)
```

</details>

### create_preflight

#### AC-5: preflight uses OPTIONS method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.method).to_equal("OPTIONS")
```

</details>

#### AC-5: preflight includes Access-Control-Request-Method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.headers).to_contain("Access-Control-Request-Method")
```

</details>

#### AC-5: Access-Control-Request-Method value matches original method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = make_cors_request("DELETE", "")
val pf = create_preflight(original)
expect(pf.headers).to_contain("DELETE")
```

</details>

#### AC-5: preflight URL matches original URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = make_cors_request("PUT", "application/json")
val pf = create_preflight(original)
expect(pf.url.host).to_equal(original.url.host)
```

</details>

### CorsChecker.validate_preflight

#### AC-5: response allowing method returns Allowed

1. make preflight response
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("PUT", "https://app.example.com")
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: response denying method returns Denied

1. make preflight response
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("GET", "https://app.example.com")
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: response with wrong origin returns Denied

1. make preflight response
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_preflight_response("PUT", "https://other.example.com")
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: response with wildcard origin returns Allowed

1. make wildcard preflight response
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight(
    make_wildcard_preflight_response("PUT")
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: method-specific response allows the requested method

1. make preflight response
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. make preflight response
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. make wildcard preflight response
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### AC-5: explicit origin allows credentialed method-specific preflight

1. make preflight response
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_method_with_credentials(
    make_preflight_response("PUT", "https://app.example.com"),
    "PUT",
    "include"
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
```

</details>

#### AC-5: header-specific response allows every requested header token

1. make header preflight response
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. make header preflight response
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_headers(
    make_header_preflight_response("Content-Type", "https://app.example.com"),
    "content-type, x-trace-id"
)
val is_denied = (result == PreflightResult.Denied)
expect(is_denied).to_equal(true)
```

</details>

#### AC-5: wildcard allow-headers permits requested headers

1. make header preflight response
   - Expected: is_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = make_checker("https://app.example.com")
val result = checker.validate_preflight_headers(
    make_header_preflight_response("*", "https://app.example.com"),
    "authorization, x-api-key"
)
val is_allowed = (result == PreflightResult.Allowed)
expect(is_allowed).to_equal(true)
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
