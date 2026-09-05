# adapter_outlook_curl_spec

> Purpose: Prove that outlook curl client.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# adapter_outlook_curl_spec

Purpose: Prove that outlook curl client.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/adapter_outlook_curl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that outlook curl client.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### outlook curl client

#### carries token and mailbox

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries token and mailbox
- Verify: carries token and mailbox
   - Expected: c.access_token equals `tk_abc`
   - Expected: c.mailbox_upn equals `ops@acme.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("carries token and mailbox")
step("Verify: carries token and mailbox")
# @req: REQ-APP-DEVHUB-001
val c = _mk_client()
expect(c.access_token).to_equal("tk_abc")
expect(c.mailbox_upn).to_equal("ops@acme.com")
```

</details>

#### defaults to the v1.0 Graph base and curl binary

- defaults to the v1.0 Graph base and curl binary
- Verify: defaults to the v1.0 Graph base and curl binary
   - Expected: c.base_url equals `https://graph.microsoft.com/v1.0`
   - Expected: c.curl_path equals `curl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults to the v1.0 Graph base and curl binary")
step("Verify: defaults to the v1.0 Graph base and curl binary")
val c = _mk_client()
expect(c.base_url).to_equal("https://graph.microsoft.com/v1.0")
expect(c.curl_path).to_equal("curl")
```

</details>

### outlook token cache

#### is fresh only when expiry clears the safety margin

- is fresh only when expiry clears the safety margin
- Verify: is fresh only when expiry clears the safety margin
   - Expected: outlook_curl_token_cache_is_fresh(1000, 900) is true
   - Expected: outlook_curl_token_cache_is_fresh(1000, 950) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is fresh only when expiry clears the safety margin")
step("Verify: is fresh only when expiry clears the safety margin")
expect(outlook_curl_token_cache_is_fresh(1000, 900)).to_equal(true)
expect(outlook_curl_token_cache_is_fresh(1000, 950)).to_equal(false)
```

</details>

#### treats the exact margin boundary as not fresh

- treats the exact margin boundary as not fresh
- Verify: treats the exact margin boundary as not fresh
   - Expected: outlook_curl_token_cache_is_fresh(1000, 940) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats the exact margin boundary as not fresh")
step("Verify: treats the exact margin boundary as not fresh")
expect(outlook_curl_token_cache_is_fresh(1000, 940)).to_equal(false)
```

</details>

#### renders and parses a token cache roundtrip

- renders and parses a token cache roundtrip
- Verify: renders and parses a token cache roundtrip
   - Expected: tok equals `tok_xyz`
   - Expected: exp equals `1700000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders and parses a token cache roundtrip")
step("Verify: renders and parses a token cache roundtrip")
val rendered = outlook_curl_render_token_cache("tok_xyz", 1700000000)
val (tok, exp) = outlook_curl_parse_token_cache(rendered)
expect(tok).to_equal("tok_xyz")
expect(exp).to_equal(1700000000)  # oracle: 1700000000 — named expected value from the requirement
```

</details>

#### parses an empty cache to empty token

- parses an empty cache to empty token
- Verify: parses an empty cache to empty token
   - Expected: tok equals ``
   - Expected: exp equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses an empty cache to empty token")
step("Verify: parses an empty cache to empty token")
val (tok, exp) = outlook_curl_parse_token_cache("")
expect(tok).to_equal("")
expect(exp).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### outlook argv builders

#### token POST uses POST verb and form content type

- token POST uses POST verb and form content type
- Verify: token POST uses POST verb and form content type
   - Expected: _list_contains(args, "-X") is true
   - Expected: _list_contains(args, "POST") is true
   - Expected: _list_contains(args, "Content-Type: application/x-www-form-urlencoded") is true
   - Expected: _list_contains(args, "grant_type=client_credentials") is true
   - Expected: _list_contains(args, "https://login/token") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("token POST uses POST verb and form content type")
step("Verify: token POST uses POST verb and form content type")
val args = _build_curl_argv_token("https://login/token", "grant_type=client_credentials")
expect(_list_contains(args, "-X")).to_equal(true)
expect(_list_contains(args, "POST")).to_equal(true)
expect(_list_contains(args, "Content-Type: application/x-www-form-urlencoded")).to_equal(true)
expect(_list_contains(args, "grant_type=client_credentials")).to_equal(true)
expect(_list_contains(args, "https://login/token")).to_equal(true)
```

</details>

#### Graph GET carries a Bearer authorization header and url

- Graph GET carries a Bearer authorization header and url
- Verify: Graph GET carries a Bearer authorization header and url
   - Expected: _list_contains(args, "Authorization: Bearer tok_abc") is true
   - Expected: _list_contains(args, "https://graph/x") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("Graph GET carries a Bearer authorization header and url")
step("Verify: Graph GET carries a Bearer authorization header and url")
val args = _build_curl_argv_get("tok_abc", "https://graph/x")
expect(_list_contains(args, "Authorization: Bearer tok_abc")).to_equal(true)
expect(_list_contains(args, "https://graph/x")).to_equal(true)
```

</details>

### outlook status mapping

#### treats 2xx as ok and others as not ok

- treats 2xx as ok and others as not ok
- Verify: treats 2xx as ok and others as not ok
   - Expected: _status_ok(200) is true
   - Expected: _status_ok(299) is true
   - Expected: _status_ok(300) is false
   - Expected: _status_ok(401) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats 2xx as ok and others as not ok")
step("Verify: treats 2xx as ok and others as not ok")
expect(_status_ok(200)).to_equal(true)
expect(_status_ok(299)).to_equal(true)
expect(_status_ok(300)).to_equal(false)
expect(_status_ok(401)).to_equal(false)
```

</details>

#### maps auth, not-found, rate-limit, server, and transport errors

- maps auth, not-found, rate-limit, server, and transport errors
- Verify: maps auth, not-found, rate-limit, server, and transport errors
   - Expected: _status_message(401, "") equals `authentication required (HTTP 401)`
   - Expected: _status_message(403, "") equals `authentication required (HTTP 403)`
   - Expected: _status_message(404, "") equals `not found (HTTP 404)`
   - Expected: _status_message(429, "") equals `rate limited (HTTP 429)`
   - Expected: _status_message(500, "boom") equals `server error (HTTP 500): boom`
   - Expected: _status_message(0, "no route") equals `transport error: no route`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps auth, not-found, rate-limit, server, and transport errors")
step("Verify: maps auth, not-found, rate-limit, server, and transport errors")
expect(_status_message(401, "")).to_equal("authentication required (HTTP 401)")
expect(_status_message(403, "")).to_equal("authentication required (HTTP 403)")
expect(_status_message(404, "")).to_equal("not found (HTTP 404)")
expect(_status_message(429, "")).to_equal("rate limited (HTTP 429)")
expect(_status_message(500, "boom")).to_equal("server error (HTTP 500): boom")
expect(_status_message(0, "no route")).to_equal("transport error: no route")
```

</details>

#### parses a numeric status tail and rejects non-numeric

- parses a numeric status tail and rejects non-numeric
- Verify: parses a numeric status tail and rejects non-numeric
   - Expected: _parse_status("200") equals `200`
   - Expected: _parse_status("  404 ") equals `404`
   - Expected: _parse_status("abc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses a numeric status tail and rejects non-numeric")
step("Verify: parses a numeric status tail and rejects non-numeric")
expect(_parse_status("200")).to_equal(200)
expect(_parse_status("  404 ")).to_equal(404)
expect(_parse_status("abc")).to_equal(0)
```

</details>

#### splits curl body from the trailing status line

- splits curl body from the trailing status line
- Verify: splits curl body from the trailing status line
   - Expected: body equals `hello world`
   - Expected: code equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("splits curl body from the trailing status line")
step("Verify: splits curl body from the trailing status line")
val (body, code) = _split_response("hello world\n200")
expect(body).to_equal("hello world")
expect(code).to_equal(200)  # oracle: 200 — named expected value from the requirement
```

</details>

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

- `REQ-SSPEC-APP`
- `REQ-APP-DEVHUB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `183ca3e1e1052e6db17c30f80ffeb0d0a5f81e08c605b56be15438aed24a8db7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `183ca3e1e1052e6db17c30f80ffeb0d0a5f81e08c605b56be15438aed24a8db7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `183ca3e1e1052e6db17c30f80ffeb0d0a5f81e08c605b56be15438aed24a8db7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/adapter_outlook_curl_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/adapter_outlook_curl_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/adapter_outlook_curl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/adapter_outlook_curl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/adapter_outlook_curl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/adapter_outlook_curl_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries token and mailbox' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/adapter_outlook_curl_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to the v1.0 Graph base and curl binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/adapter_outlook_curl_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is fresh only when expiry clears the safety margin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
