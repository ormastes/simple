# adapter_jira_curl_spec

> Purpose: Prove that Jira curl adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# adapter_jira_curl_spec

Purpose: Prove that Jira curl adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/adapter_jira_curl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Jira curl adapter.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Jira curl adapter

#### JiraClient.auth_header

#### produces a Basic <base64> header for known vector

- produces a Basic <base64> header for known vector
- Verify: produces a Basic <base64> header for known vector
   - Expected: header.starts_with("Basic ") is true
   - Expected: header equals `Basic YWxpY2VAZXhhbXBsZS5jb206dG9rLTEyMw==`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("produces a Basic <base64> header for known vector")
step("Verify: produces a Basic <base64> header for known vector")
# @req: REQ-APP-DEVHUB-001
# base64("alice@example.com:tok-123") = YWxpY2VAZXhhbXBsZS5jb206dG9rLTEyMw==
# Verified independently with `printf '...' | base64`.
val client = JiraClient(
    base_url: "https://acme.atlassian.net",
    email: "alice@example.com",
    api_token: "tok-123",
    curl_path: "curl",
)
val header = client.auth_header()
expect(header.starts_with("Basic ")).to_equal(true)
expect(header).to_equal("Basic YWxpY2VAZXhhbXBsZS5jb206dG9rLTEyMw==")
```

</details>

#### returns empty string when email is missing

- returns empty string when email is missing
- Verify: returns empty string when email is missing
   - Expected: client.auth_header() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns empty string when email is missing")
step("Verify: returns empty string when email is missing")
val client = JiraClient(base_url: "https://x", email: "", api_token: "tok", curl_path: "curl")
expect(client.auth_header()).to_equal("")
```

</details>

#### returns empty string when token is missing

- returns empty string when token is missing
- Verify: returns empty string when token is missing
   - Expected: client.auth_header() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns empty string when token is missing")
step("Verify: returns empty string when token is missing")
val client = JiraClient(base_url: "https://x", email: "a@b", api_token: "", curl_path: "curl")
expect(client.auth_header()).to_equal("")
```

</details>

#### argv builders

#### GET argv contains literal %\{http_code\} write-out token

- GET argv contains literal %\{http_code\} write-out token
- Verify: GET argv contains literal %(http_code) write-out token
   - Expected: argv contains `\n%\{http_code\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("GET argv contains literal %\{http_code\} write-out token")
step("Verify: GET argv contains literal %(http_code) write-out token")
# Brace-escape regression check: the argv must carry the
# literal `%{http_code}` so curl emits the numeric status.
# If a future change silently interpolates the braces or
# strips the backslashes, this test catches it.
val argv = _build_curl_argv_get("Basic xyz", "https://x/rest/api/3/issue/X-1")
expect(argv.contains("\n%\{http_code\}")).to_equal(true)
```

</details>

#### GET argv carries Authorization and Accept headers

- GET argv carries Authorization and Accept headers
- Verify: GET argv carries Authorization and Accept headers
   - Expected: argv contains `Authorization: Basic xyz`
   - Expected: argv contains `Accept: application/json`
   - Expected: argv[argv.len() - 1] equals `https://x/rest/api/3/issue/X-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("GET argv carries Authorization and Accept headers")
step("Verify: GET argv carries Authorization and Accept headers")
val argv = _build_curl_argv_get("Basic xyz", "https://x/rest/api/3/issue/X-1")
expect(argv.contains("Authorization: Basic xyz")).to_equal(true)
expect(argv.contains("Accept: application/json")).to_equal(true)
expect(argv[argv.len() - 1]).to_equal("https://x/rest/api/3/issue/X-1")
```

</details>

#### POST argv adds -X POST and Content-Type

- POST argv adds -X POST and Content-Type
- Verify: POST argv adds -X POST and Content-Type
   - Expected: argv contains `-X`
   - Expected: argv contains `POST`
   - Expected: argv contains `Content-Type: application/json`
   - Expected: argv contains `{"jql":"k"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("POST argv adds -X POST and Content-Type")
step("Verify: POST argv adds -X POST and Content-Type")
val argv = _build_curl_argv_post("Basic z", "https://x/rest/api/3/search/jql", "{\"jql\":\"k\"}")
expect(argv.contains("-X")).to_equal(true)
expect(argv.contains("POST")).to_equal(true)
expect(argv.contains("Content-Type: application/json")).to_equal(true)
expect(argv.contains("{\"jql\":\"k\"}")).to_equal(true)
```

</details>

#### PUT argv adds -X PUT and Content-Type (J2 update)

- PUT argv adds -X PUT and Content-Type (J2 update)
- Verify: PUT argv adds -X PUT and Content-Type (J2 update)
   - Expected: argv contains `-X`
   - Expected: argv contains `PUT`
   - Expected: argv contains `Content-Type: application/json`
   - Expected: argv contains `{"fields":{"summary":"k"}}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("PUT argv adds -X PUT and Content-Type (J2 update)")
step("Verify: PUT argv adds -X PUT and Content-Type (J2 update)")
val argv = _build_curl_argv_put("Basic z", "https://x/rest/api/3/issue/X-1", "{\"fields\":{\"summary\":\"k\"}}")
expect(argv.contains("-X")).to_equal(true)
expect(argv.contains("PUT")).to_equal(true)
expect(argv.contains("Content-Type: application/json")).to_equal(true)
expect(argv.contains("{\"fields\":{\"summary\":\"k\"}}")).to_equal(true)
```

</details>

#### download argv uses -L -o and writes status without leading newline

- download argv uses -L -o and writes status without leading newline
- Verify: download argv uses -L -o and writes status without leading newline
   - Expected: argv contains `-L`
   - Expected: argv contains `-o`
   - Expected: argv contains `/tmp/out.bin`
   - Expected: argv contains `%\{http_code\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("download argv uses -L -o and writes status without leading newline")
step("Verify: download argv uses -L -o and writes status without leading newline")
val argv = _build_curl_argv_download("Basic z", "https://x/rest/api/3/attachment/content/123", "/tmp/out.bin")
expect(argv.contains("-L")).to_equal(true)
expect(argv.contains("-o")).to_equal(true)
expect(argv.contains("/tmp/out.bin")).to_equal(true)
# download argv intentionally omits the "\n" prefix
expect(argv.contains("%\{http_code\}")).to_equal(true)
```

</details>

#### _split_response

#### splits body and trailing 200 status

- splits body and trailing 200 status
- Verify: splits body and trailing 200 status
   - Expected: body equals `{"ok":true}`
   - Expected: code equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("splits body and trailing 200 status")
step("Verify: splits body and trailing 200 status")
val (body, code) = _split_response("{\"ok\":true}\n200")
expect(body).to_equal("{\"ok\":true}")
expect(code).to_equal(200)  # oracle: 200 — named expected value from the requirement
```

</details>

#### handles 404 status

- handles 404 status
- Verify: handles 404 status
   - Expected: code equals `404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles 404 status")
step("Verify: handles 404 status")
val (_b, code) = _split_response("\n404")
expect(code).to_equal(404)  # oracle: 404 — named expected value from the requirement
```

</details>

#### returns (\

- returns (\
   - Expected: b equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns (\")
val (b, code) = _split_response("")
expect(b).to_equal("")
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns (whole, 0) on no-newline non-numeric output

- returns (whole, 0) on no-newline non-numeric output
- Verify: returns (whole, 0) on no-newline non-numeric output
   - Expected: b equals `garbage`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns (whole, 0) on no-newline non-numeric output")
step("Verify: returns (whole, 0) on no-newline non-numeric output")
val (b, code) = _split_response("garbage")
expect(b).to_equal("garbage")
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### treats no-newline 3-digit-only as just a status

- treats no-newline 3-digit-only as just a status
- Verify: treats no-newline 3-digit-only as just a status
   - Expected: b equals ``
   - Expected: code equals `204`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats no-newline 3-digit-only as just a status")
step("Verify: treats no-newline 3-digit-only as just a status")
val (b, code) = _split_response("204")
expect(b).to_equal("")
expect(code).to_equal(204)  # oracle: 204 — named expected value from the requirement
```

</details>

#### _parse_status

#### parses 200

- parses 200
- Verify: parses 200
   - Expected: _parse_status("200") equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses 200")
step("Verify: parses 200")
expect(_parse_status("200")).to_equal(200)
```

</details>

#### rejects non-digits

- rejects non-digits
- Verify: rejects non-digits
   - Expected: _parse_status("abc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects non-digits")
step("Verify: rejects non-digits")
expect(_parse_status("abc")).to_equal(0)
```

</details>

#### rejects too-short input

- rejects too-short input
- Verify: rejects too-short input
   - Expected: _parse_status("12") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects too-short input")
step("Verify: rejects too-short input")
expect(_parse_status("12")).to_equal(0)
```

</details>

#### _status_ok

#### 200 is ok

- 200 is ok
- Verify: 200 is ok
   - Expected: _status_ok(200) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("200 is ok")
step("Verify: 200 is ok")
expect(_status_ok(200)).to_equal(true)
```

</details>

#### 299 is ok

- 299 is ok
- Verify: 299 is ok
   - Expected: _status_ok(299) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("299 is ok")
step("Verify: 299 is ok")
expect(_status_ok(299)).to_equal(true)
```

</details>

#### 300 is not ok

- 300 is not ok
- Verify: 300 is not ok
   - Expected: _status_ok(300) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("300 is not ok")
step("Verify: 300 is not ok")
expect(_status_ok(300)).to_equal(false)
```

</details>

#### 401 is not ok

- 401 is not ok
- Verify: 401 is not ok
   - Expected: _status_ok(401) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("401 is not ok")
step("Verify: 401 is not ok")
expect(_status_ok(401)).to_equal(false)
```

</details>

#### _status_message

#### 401 -> auth required

- 401 -> auth required
- Verify: 401 -> auth required
   - Expected: msg contains `authentication required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("401 -> auth required")
step("Verify: 401 -> auth required")
val msg = _status_message(401, "")
expect(msg.contains("authentication required")).to_equal(true)
```

</details>

#### 404 -> not found

- 404 -> not found
- Verify: 404 -> not found
   - Expected: _status_message(404, "") contains `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("404 -> not found")
step("Verify: 404 -> not found")
expect(_status_message(404, "").contains("not found")).to_equal(true)
```

</details>

#### 429 -> rate limited

- 429 -> rate limited
- Verify: 429 -> rate limited
   - Expected: _status_message(429, "") contains `rate limited`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("429 -> rate limited")
step("Verify: 429 -> rate limited")
expect(_status_message(429, "").contains("rate limited")).to_equal(true)
```

</details>

#### 500 -> server error

- 500 -> server error
- Verify: 500 -> server error
   - Expected: _status_message(500, "boom") contains `server error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("500 -> server error")
step("Verify: 500 -> server error")
expect(_status_message(500, "boom").contains("server error")).to_equal(true)
```

</details>

#### 0 -> transport error

- 0 -> transport error
- Verify: 0 -> transport error
   - Expected: _status_message(0, "no route") contains `transport error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("0 -> transport error")
step("Verify: 0 -> transport error")
expect(_status_message(0, "no route").contains("transport error")).to_equal(true)
```

</details>

#### _adf_doc

#### wraps plain text in an ADF document with type doc

- wraps plain text in an ADF document with type doc
- Verify: wraps plain text in an ADF document with type doc
   - Expected: adf contains `"type":"doc"`
   - Expected: adf contains `"version":1`
   - Expected: adf contains `"type":"paragraph"`
   - Expected: adf contains `"text":"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps plain text in an ADF document with type doc")
step("Verify: wraps plain text in an ADF document with type doc")
val adf = _adf_doc("hello")
expect(adf.contains("\"type\":\"doc\"")).to_equal(true)
expect(adf.contains("\"version\":1")).to_equal(true)
expect(adf.contains("\"type\":\"paragraph\"")).to_equal(true)
expect(adf.contains("\"text\":\"hello\"")).to_equal(true)
```

</details>

#### escapes embedded quotes

- escapes embedded quotes
- Verify: escapes embedded quotes
   - Expected: adf contains `\\"hi\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes embedded quotes")
step("Verify: escapes embedded quotes")
val adf = _adf_doc("she said \"hi\"")
expect(adf.contains("\\\"hi\\\"")).to_equal(true)
```

</details>

#### _json_escape

#### escapes a backslash

- escapes a backslash
- Verify: escapes a backslash
   - Expected: _json_escape("a\\b") equals `a\\\\b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes a backslash")
step("Verify: escapes a backslash")
expect(_json_escape("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes a quote

- escapes a quote
- Verify: escapes a quote
   - Expected: _json_escape("a\"b") equals `a\\"b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes a quote")
step("Verify: escapes a quote")
expect(_json_escape("a\"b")).to_equal("a\\\"b")
```

</details>

#### escapes a newline

- escapes a newline
- Verify: escapes a newline
   - Expected: _json_escape("a\nb") equals `a\\nb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes a newline")
step("Verify: escapes a newline")
expect(_json_escape("a\nb")).to_equal("a\\nb")
```

</details>

#### _normalize_base

#### leaves a clean URL alone

- leaves a clean URL alone
- Verify: leaves a clean URL alone
   - Expected: _normalize_base("https://x.atlassian.net") equals `https://x.atlassian.net`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves a clean URL alone")
step("Verify: leaves a clean URL alone")
expect(_normalize_base("https://x.atlassian.net")).to_equal("https://x.atlassian.net")
```

</details>

#### strips a trailing slash

- strips a trailing slash
- Verify: strips a trailing slash
   - Expected: _normalize_base("https://x.atlassian.net/") equals `https://x.atlassian.net`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("strips a trailing slash")
step("Verify: strips a trailing slash")
expect(_normalize_base("https://x.atlassian.net/")).to_equal("https://x.atlassian.net")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `106cb460e4d4d1e44e1c65bad014135068ad34866f60f945438f721cd50124a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `106cb460e4d4d1e44e1c65bad014135068ad34866f60f945438f721cd50124a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `106cb460e4d4d1e44e1c65bad014135068ad34866f60f945438f721cd50124a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/adapter_jira_curl_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/adapter_jira_curl_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/adapter_jira_curl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/adapter_jira_curl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/adapter_jira_curl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/adapter_jira_curl_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a Basic <base64> header for known vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/adapter_jira_curl_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string when email is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/adapter_jira_curl_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string when token is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
