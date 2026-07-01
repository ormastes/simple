# Adapter Jira Curl Specification

> <details>

<!-- sdn-diagram:id=adapter_jira_curl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_jira_curl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_jira_curl_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_jira_curl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Jira Curl Specification

## Scenarios

### Jira curl adapter

#### JiraClient.auth_header

#### produces a Basic <base64> header for known vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = JiraClient(base_url: "https://x", email: "", api_token: "tok", curl_path: "curl")
expect(client.auth_header()).to_equal("")
```

</details>

#### returns empty string when token is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = JiraClient(base_url: "https://x", email: "a@b", api_token: "", curl_path: "curl")
expect(client.auth_header()).to_equal("")
```

</details>

#### argv builders

#### GET argv contains literal %\{http_code\} write-out token

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Brace-escape regression check: the argv must carry the
# literal `%{http_code}` so curl emits the numeric status.
# If a future change silently interpolates the braces or
# strips the backslashes, this test catches it.
val argv = _build_curl_argv_get("Basic xyz", "https://x/rest/api/3/issue/X-1")
expect(argv.contains("\n%\{http_code\}")).to_equal(true)
```

</details>

#### GET argv carries Authorization and Accept headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _build_curl_argv_get("Basic xyz", "https://x/rest/api/3/issue/X-1")
expect(argv.contains("Authorization: Basic xyz")).to_equal(true)
expect(argv.contains("Accept: application/json")).to_equal(true)
expect(argv[argv.len() - 1]).to_equal("https://x/rest/api/3/issue/X-1")
```

</details>

#### POST argv adds -X POST and Content-Type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _build_curl_argv_post("Basic z", "https://x/rest/api/3/search/jql", "{\"jql\":\"k\"}")
expect(argv.contains("-X")).to_equal(true)
expect(argv.contains("POST")).to_equal(true)
expect(argv.contains("Content-Type: application/json")).to_equal(true)
expect(argv.contains("{\"jql\":\"k\"}")).to_equal(true)
```

</details>

#### download argv uses -L -o and writes status without leading newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (body, code) = _split_response("{\"ok\":true}\n200")
expect(body).to_equal("{\"ok\":true}")
expect(code).to_equal(200)
```

</details>

#### handles 404 status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_b, code) = _split_response("\n404")
expect(code).to_equal(404)
```

</details>

#### returns (\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (b, code) = _split_response("")
expect(b).to_equal("")
expect(code).to_equal(0)
```

</details>

#### returns (whole, 0) on no-newline non-numeric output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (b, code) = _split_response("garbage")
expect(b).to_equal("garbage")
expect(code).to_equal(0)
```

</details>

#### treats no-newline 3-digit-only as just a status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (b, code) = _split_response("204")
expect(b).to_equal("")
expect(code).to_equal(204)
```

</details>

#### _parse_status

#### parses 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_status("200")).to_equal(200)
```

</details>

#### rejects non-digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_status("abc")).to_equal(0)
```

</details>

#### rejects too-short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_status("12")).to_equal(0)
```

</details>

#### _status_ok

#### 200 is ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_ok(200)).to_equal(true)
```

</details>

#### 299 is ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_ok(299)).to_equal(true)
```

</details>

#### 300 is not ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_ok(300)).to_equal(false)
```

</details>

#### 401 is not ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_ok(401)).to_equal(false)
```

</details>

#### _status_message

#### 401 -> auth required

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _status_message(401, "")
expect(msg.contains("authentication required")).to_equal(true)
```

</details>

#### 404 -> not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_message(404, "").contains("not found")).to_equal(true)
```

</details>

#### 429 -> rate limited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_message(429, "").contains("rate limited")).to_equal(true)
```

</details>

#### 500 -> server error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_message(500, "boom").contains("server error")).to_equal(true)
```

</details>

#### 0 -> transport error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_message(0, "no route").contains("transport error")).to_equal(true)
```

</details>

#### _adf_doc

#### wraps plain text in an ADF document with type doc

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adf = _adf_doc("hello")
expect(adf.contains("\"type\":\"doc\"")).to_equal(true)
expect(adf.contains("\"version\":1")).to_equal(true)
expect(adf.contains("\"type\":\"paragraph\"")).to_equal(true)
expect(adf.contains("\"text\":\"hello\"")).to_equal(true)
```

</details>

#### escapes embedded quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adf = _adf_doc("she said \"hi\"")
expect(adf.contains("\\\"hi\\\"")).to_equal(true)
```

</details>

#### _json_escape

#### escapes a backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_json_escape("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes a quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_json_escape("a\"b")).to_equal("a\\\"b")
```

</details>

#### escapes a newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_json_escape("a\nb")).to_equal("a\\nb")
```

</details>

#### _normalize_base

#### leaves a clean URL alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_normalize_base("https://x.atlassian.net")).to_equal("https://x.atlassian.net")
```

</details>

#### strips a trailing slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_normalize_base("https://x.atlassian.net/")).to_equal("https://x.atlassian.net")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_jira_curl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jira curl adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
