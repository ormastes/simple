# Csrf Specification

> Tests covering CSRF token generation, CSRF token constant-time comparison, CsrfConfig defaults, csrf_handler exempt methods pass through, csrf_handler fail-closed on empty secret, CSRF header and cookie helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Csrf Specification

## Scenarios

### CSRF token generation

#### returns empty string when secret_key is empty (fail-closed)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns empty string when secret_key is empty (fail-closed)
   - Expected: token equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string when secret_key is empty (fail-closed)")
val config = CsrfConfig.default()
val token = generate_csrf_token(config, "session-abc")
expect(token).to_equal("")
```

</details>

#### generate_csrf_token_with_timestamp returns empty when secret_key is empty

- generate_csrf_token_with_timestamp returns empty when secret_key is empty
   - Expected: token equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("generate_csrf_token_with_timestamp returns empty when secret_key is empty")
val config = CsrfConfig.default()
val token = generate_csrf_token_with_timestamp(config, "session-abc", 1000000)
expect(token).to_equal("")
```

</details>

### CSRF token constant-time comparison

#### identical strings compare equal

- identical strings compare equal
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("identical strings compare equal")
val token = "abc123def456ghi789jkl012mno345pq"
val result = constant_time_eq(token, token)
expect(result).to_equal(true)
```

</details>

#### mismatched tokens compare unequal

- mismatched tokens compare unequal
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mismatched tokens compare unequal")
val token_a = "abc123def456ghi789jkl012mno345pq"
val token_b = "zzz999yyy888xxx777www666vvv555uu"
val result = constant_time_eq(token_a, token_b)
expect(result).to_equal(false)
```

</details>

#### empty string does not equal a non-empty token

- empty string does not equal a non-empty token
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty string does not equal a non-empty token")
val token = "abc123def456ghi789jkl012mno345pq"
val result = constant_time_eq("", token)
expect(result).to_equal(false)
```

</details>

#### both empty strings compare equal

- both empty strings compare equal
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("both empty strings compare equal")
val result = constant_time_eq("", "")
expect(result).to_equal(true)
```

</details>

### CsrfConfig defaults

#### default config has empty secret_key

- default config has empty secret_key
   - Expected: config.secret_key equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default config has empty secret_key")
val config = CsrfConfig.default()
expect(config.secret_key).to_equal("")
```

</details>

#### default config uses X-CSRF-Token header

- default config uses X-CSRF-Token header
   - Expected: config.token_header equals `X-CSRF-Token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default config uses X-CSRF-Token header")
val config = CsrfConfig.default()
expect(config.token_header).to_equal("X-CSRF-Token")
```

</details>

#### default config uses csrf_token cookie

- default config uses csrf_token cookie
   - Expected: config.cookie_name equals `csrf_token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default config uses csrf_token cookie")
val config = CsrfConfig.default()
expect(config.cookie_name).to_equal("csrf_token")
```

</details>

#### default exempt_methods includes GET

- default exempt_methods includes GET
   - Expected: has_get is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default exempt_methods includes GET")
val config = CsrfConfig.default()
val has_get = config.exempt_methods.contains("GET")
expect(has_get).to_equal(true)
```

</details>

#### default exempt_methods includes HEAD

- default exempt_methods includes HEAD
   - Expected: has_head is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default exempt_methods includes HEAD")
val config = CsrfConfig.default()
val has_head = config.exempt_methods.contains("HEAD")
expect(has_head).to_equal(true)
```

</details>

#### default exempt_methods includes OPTIONS

- default exempt_methods includes OPTIONS
   - Expected: has_options is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default exempt_methods includes OPTIONS")
val config = CsrfConfig.default()
val has_options = config.exempt_methods.contains("OPTIONS")
expect(has_options).to_equal(true)
```

</details>

#### default exempt_methods does not include POST

- default exempt_methods does not include POST
   - Expected: has_post is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default exempt_methods does not include POST")
val config = CsrfConfig.default()
val has_post = config.exempt_methods.contains("POST")
expect(has_post).to_equal(false)
```

</details>

#### default exempt_methods does not include DELETE

- default exempt_methods does not include DELETE
   - Expected: has_delete is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("default exempt_methods does not include DELETE")
val config = CsrfConfig.default()
val has_delete = config.exempt_methods.contains("DELETE")
expect(has_delete).to_equal(false)
```

</details>

### csrf_handler exempt methods pass through

#### GET request continues without CSRF check

- GET request continues without CSRF check
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("GET request continues without CSRF check")
val config = _test_config()
val server_config = _test_server_config()
val request = _test_request("GET", "/", [])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Continue:
        expect(true).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

#### HEAD request continues without CSRF check

- HEAD request continues without CSRF check
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("HEAD request continues without CSRF check")
val config = _test_config()
val server_config = _test_server_config()
val request = _test_request("HEAD", "/", [])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Continue:
        expect(true).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

#### OPTIONS request continues without CSRF check

- OPTIONS request continues without CSRF check
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("OPTIONS request continues without CSRF check")
val config = _test_config()
val server_config = _test_server_config()
val request = _test_request("OPTIONS", "/", [])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Continue:
        expect(true).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

### csrf_handler fail-closed on empty secret

#### POST with empty secret_key returns Error(403)

- POST with empty secret_key returns Error(403)
   - Expected: status equals `403`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POST with empty secret_key returns Error(403)")
val config = CsrfConfig.default()
val server_config = _test_server_config()
val request = _test_request("POST", "/api/data",
    [("X-CSRF-Token", "sometoken"), ("Cookie", "csrf_token=sometoken")])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Error(status, _):
        expect(status).to_equal(403)
    _:
        expect(false).to_equal(true)
```

</details>

#### PUT with empty secret_key returns Error(403)

- PUT with empty secret_key returns Error(403)
   - Expected: status equals `403`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("PUT with empty secret_key returns Error(403)")
val config = CsrfConfig.default()
val server_config = _test_server_config()
val request = _test_request("PUT", "/api/data",
    [("X-CSRF-Token", "sometoken"), ("Cookie", "csrf_token=sometoken")])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Error(status, _):
        expect(status).to_equal(403)
    _:
        expect(false).to_equal(true)
```

</details>

### CSRF header and cookie helpers

#### get_header_value finds a header case-insensitively

- get_header_value finds a header case-insensitively
   - Expected: result equals `mytoken123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_header_value finds a header case-insensitively")
val headers = [("X-CSRF-Token", "mytoken123")]
val result = get_header_value(headers, "x-csrf-token")
expect(result).to_equal("mytoken123")
```

</details>

#### get_header_value returns empty when header not found

- get_header_value returns empty when header not found
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_header_value returns empty when header not found")
val headers = [("Content-Type", "text/html")]
val result = get_header_value(headers, "X-CSRF-Token")
expect(result).to_equal("")
```

</details>

#### get_cookie_value extracts named cookie

- get_cookie_value extracts named cookie
   - Expected: result equals `tok456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_cookie_value extracts named cookie")
val headers = [("Cookie", "session=abc; csrf_token=tok456")]
val result = get_cookie_value(headers, "csrf_token")
expect(result).to_equal("tok456")
```

</details>

#### get_cookie_value returns empty when cookie not found

- get_cookie_value returns empty when cookie not found
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_cookie_value returns empty when cookie not found")
val headers = [("Cookie", "session=abc")]
val result = get_cookie_value(headers, "csrf_token")
expect(result).to_equal("")
```

</details>

#### get_cookie_value returns empty when no Cookie header present

- get_cookie_value returns empty when no Cookie header present
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_cookie_value returns empty when no Cookie header present")
val headers = [("Content-Type", "application/json")]
val result = get_cookie_value(headers, "csrf_token")
expect(result).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/csrf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSRF token generation, CSRF token constant-time comparison, CsrfConfig defaults, csrf_handler exempt methods pass through, csrf_handler fail-closed on empty secret, CSRF header and cookie helpers.
- CSRF token generation
- CSRF token constant-time comparison
- CsrfConfig defaults
- csrf_handler exempt methods pass through
- csrf_handler fail-closed on empty secret
- CSRF header and cookie helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `d5a59def046cfe1a7598a4b4247fa7abcf0c3f87ecad0fe125fcf006b8bf637d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5a59def046cfe1a7598a4b4247fa7abcf0c3f87ecad0fe125fcf006b8bf637d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5a59def046cfe1a7598a4b4247fa7abcf0c3f87ecad0fe125fcf006b8bf637d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/http_server/csrf_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/csrf_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/csrf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/csrf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/csrf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/http_server/csrf_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string when secret_key is empty (fail-closed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/csrf_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generate_csrf_token_with_timestamp returns empty when secret_key is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/csrf_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical strings compare equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
