# Adapter Bitbucket Curl Specification

> <details>

<!-- sdn-diagram:id=adapter_bitbucket_curl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_bitbucket_curl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_bitbucket_curl_spec -> app
adapter_bitbucket_curl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_bitbucket_curl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Bitbucket Curl Specification

## Scenarios

### bbc auth header

#### builds Bearer when token present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bbc_auth_header("abc123")).to_equal("Bearer abc123")
```

</details>

#### returns empty when token blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bbc_auth_header("")).to_equal("")
```

</details>

#### client.auth_header() forwards to bbc_auth_header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(c.auth_header()).to_equal("Bearer tk_abc")
```

</details>

#### is_configured true when ws+repo+token set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(c.is_configured()).to_equal(true)
```

</details>

#### is_configured false when token blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = BbCurlClient(base_url: "x", workspace: "w", repo: "r", token: "", curl_path: "curl")
expect(c.is_configured()).to_equal(false)
```

</details>

#### is_configured false when workspace blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = BbCurlClient(base_url: "x", workspace: "", repo: "r", token: "t", curl_path: "curl")
expect(c.is_configured()).to_equal(false)
```

</details>

### bbc URL builders

#### PR collection URL has /pullrequests suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(bbc_pr_collection_url(c)).to_equal("https://api.bitbucket.org/2.0/repositories/acme/widgets/pullrequests")
```

</details>

#### PR resource URL appends id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(bbc_pr_url(c, 42)).to_equal("https://api.bitbucket.org/2.0/repositories/acme/widgets/pullrequests/42")
```

</details>

#### PR comments sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(bbc_pr_sub_url(c, 7, "comments")).to_end_with("/pullrequests/7/comments")
```

</details>

#### PR approve sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(bbc_pr_sub_url(c, 7, "approve")).to_end_with("/pullrequests/7/approve")
```

</details>

#### PR merge sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(bbc_pr_sub_url(c, 7, "merge")).to_end_with("/pullrequests/7/merge")
```

</details>

#### PR statuses sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(bbc_pr_sub_url(c, 7, "statuses")).to_end_with("/pullrequests/7/statuses")
```

</details>

### _argv_curl_get

#### uses GET verb with -s -S

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_get("https://x/foo", "Bearer t")
expect(_list_contains(args, "-X")).to_equal(true)
expect(_list_contains(args, "GET")).to_equal(true)
expect(_list_contains(args, "-s")).to_equal(true)
expect(_list_contains(args, "-S")).to_equal(true)
```

</details>

#### includes Authorization header when auth non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_get("https://x/foo", "Bearer t")
expect(_list_contains(args, "Authorization: Bearer t")).to_equal(true)
```

</details>

#### omits Authorization header when auth empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_get("https://x/foo", "")
expect(_list_contains(args, "Authorization: ")).to_equal(false)
```

</details>

#### includes Accept: application/json

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_get("https://x/foo", "")
expect(_list_contains(args, "Accept: application/json")).to_equal(true)
```

</details>

#### uses curl http_code write-out built without interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_get("https://x/foo", "")
# The runtime-built literal must equal the curl write-out string.
val expected = "\n" + "%" + "{" + "http_code" + "}"
expect(_list_contains(args, expected)).to_equal(true)
```

</details>

#### url is the last arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_get("https://x/foo", "")
expect(args[args.len() - 1]).to_equal("https://x/foo")
```

</details>

### _argv_curl_post

#### uses POST verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_post("https://x/foo", "Bearer t", "{}")
expect(_list_contains(args, "POST")).to_equal(true)
```

</details>

#### includes Content-Type for JSON body

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_post("https://x/foo", "Bearer t", "{}")
expect(_list_contains(args, "Content-Type: application/json")).to_equal(true)
```

</details>

#### passes body via -d when non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_post("https://x/foo", "Bearer t", "{\"a\":1}")
expect(_list_contains(args, "-d")).to_equal(true)
expect(_list_contains(args, "{\"a\":1}")).to_equal(true)
```

</details>

#### omits -d entirely when body is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_post("https://x/foo", "Bearer t", "")
expect(_list_contains(args, "-d")).to_equal(false)
```

</details>

#### url is the last arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_post("https://x/foo", "Bearer t", "")
expect(args[args.len() - 1]).to_equal("https://x/foo")
```

</details>

### _argv_curl_delete

#### uses DELETE verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_delete("https://x/foo", "Bearer t")
expect(_list_contains(args, "DELETE")).to_equal(true)
```

</details>

#### does NOT include -d (DELETE has no body here)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_delete("https://x/foo", "Bearer t")
expect(_list_contains(args, "-d")).to_equal(false)
```

</details>

#### url is the last arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _argv_curl_delete("https://x/foo", "Bearer t")
expect(args[args.len() - 1]).to_equal("https://x/foo")
```

</details>

### bb_build_create_pr_body

#### minimum body has title and source branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("My PR", "feat-x", "", [])
expect(body).to_contain("\"title\": \"My PR\"")
expect(body).to_contain("\"name\": \"feat-x\"")
expect(json_parse(body) != nil).to_equal(true)
```

</details>

#### omits destination when blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("T", "src", "", [])
expect(body.contains("\"destination\":")).to_equal(false)
```

</details>

#### includes reviewers as uuid objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("T", "src", "main", ["uuid-aaa", "uuid-bbb"])
expect(body).to_contain("\"uuid\": \"uuid-aaa\"")
expect(body).to_contain("\"uuid\": \"uuid-bbb\"")
```

</details>

### bb_build_comment_body

#### general comment has no inline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("Looks good", "", -1, -1)
expect(body).to_contain("\"raw\": \"Looks good\"")
expect(body.contains("\"inline\":")).to_equal(false)
```

</details>

#### inline comment encodes from=null when negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("Bug", "src/x.spl", -1, 42)
expect(body).to_contain("\"from\": null")
expect(body).to_contain("\"to\": 42")
```

</details>

### bb_build_merge_body

#### squash + close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_merge_body("squash", true, "")
expect(body).to_contain("\"merge_strategy\": \"squash\"")
expect(body).to_contain("\"close_source_branch\": true")
```

</details>

### _bbc_parse_status_tail

#### splits body and trailing http_code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, body) = _bbc_parse_status_tail("{\"id\": 1}\n200")
expect(status).to_equal(200)
expect(body).to_equal("{\"id\": 1}")
```

</details>

#### handles a multi-line body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, body) = _bbc_parse_status_tail("line1\nline2\nline3\n404")
expect(status).to_equal(404)
expect(body).to_equal("line1\nline2\nline3")
```

</details>

#### handles 5xx codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, _body) = _bbc_parse_status_tail("err\n503")
expect(status).to_equal(503)
```

</details>

#### returns (0, raw) when tail is non-numeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, body) = _bbc_parse_status_tail("only-output-no-code")
expect(status).to_equal(0)
expect(body).to_equal("")
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, body) = _bbc_parse_status_tail("")
expect(status).to_equal(0)
expect(body).to_equal("")
```

</details>

### _bbc_status_label

#### 401 → blocked-auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(401, "no token", BB_OP_GENERAL)
expect(s).to_contain("blocked-auth")
expect(s).to_contain("401")
```

</details>

#### 403 on merge → branch policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(403, "branch restriction", BB_OP_MERGE)
expect(s).to_contain("blocked")
expect(s).to_contain("branch policy")
```

</details>

#### 403 on general → blocked-auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(403, "no scope", BB_OP_GENERAL)
expect(s).to_contain("blocked-auth")
expect(s).to_contain("403")
```

</details>

#### 404 → not_found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(404, "", BB_OP_GENERAL)
expect(s).to_contain("not_found")
```

</details>

#### 409 → blocked-conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(409, "merge conflict", BB_OP_GENERAL)
expect(s).to_contain("blocked-conflict")
```

</details>

#### 429 → rate_limited

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(429, "", BB_OP_GENERAL)
expect(s).to_contain("rate_limited")
```

</details>

#### 500 → api_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(500, "boom", BB_OP_GENERAL)
expect(s).to_contain("api_error")
expect(s).to_contain("500")
```

</details>

#### 0 (curl process error) → network_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _bbc_status_label(0, "curl: not found", BB_OP_GENERAL)
expect(s).to_contain("network_error")
```

</details>

### bbc ready-to-merge (via shared bb_eval_ready_to_merge)

#### ready when OPEN + approved + statuses SUCCESSFUL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (ready, _reason) = bb_eval_ready_to_merge(json_parse(FIXTURE_PR_APPROVED_OPEN), json_parse(FIXTURE_STATUSES_OK))
expect(ready).to_equal(true)
```

</details>

#### not ready when no approval

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (ready, reason) = bb_eval_ready_to_merge(json_parse(FIXTURE_PR_PENDING), json_parse(FIXTURE_STATUSES_OK))
expect(ready).to_equal(false)
expect(reason).to_contain("no approved reviewers")
```

</details>

#### not ready when a status FAILED

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (ready, reason) = bb_eval_ready_to_merge(json_parse(FIXTURE_PR_APPROVED_OPEN), json_parse(FIXTURE_STATUSES_FAIL))
expect(ready).to_equal(false)
expect(reason).to_contain("FAILED")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_bitbucket_curl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bbc auth header
- bbc URL builders
- _argv_curl_get
- _argv_curl_post
- _argv_curl_delete
- bb_build_create_pr_body
- bb_build_comment_body
- bb_build_merge_body
- _bbc_parse_status_tail
- _bbc_status_label
- bbc ready-to-merge (via shared bb_eval_ready_to_merge)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
