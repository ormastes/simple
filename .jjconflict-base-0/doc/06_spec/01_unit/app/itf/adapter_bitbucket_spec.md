# Adapter Bitbucket Specification

> <details>

<!-- sdn-diagram:id=adapter_bitbucket_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_bitbucket_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_bitbucket_spec -> app
adapter_bitbucket_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_bitbucket_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Bitbucket Specification

## Scenarios

### bb URL builders

#### PR collection URL has /pullrequests suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = bb_pr_collection_url("acme", "widgets")
expect(u).to_equal("https://api.bitbucket.org/2.0/repositories/acme/widgets/pullrequests")
```

</details>

#### PR resource URL appends id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = bb_pr_url("acme", "widgets", 42)
expect(u).to_equal("https://api.bitbucket.org/2.0/repositories/acme/widgets/pullrequests/42")
```

</details>

#### PR comments sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = bb_pr_sub_url("acme", "widgets", 42, "comments")
expect(u).to_end_with("/pullrequests/42/comments")
```

</details>

#### PR approve sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = bb_pr_sub_url("acme", "widgets", 7, "approve")
expect(u).to_equal("https://api.bitbucket.org/2.0/repositories/acme/widgets/pullrequests/7/approve")
```

</details>

#### PR merge sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = bb_pr_sub_url("acme", "widgets", 7, "merge")
expect(u).to_end_with("/pullrequests/7/merge")
```

</details>

#### PR statuses sub URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = bb_pr_sub_url("acme", "widgets", 7, "statuses")
expect(u).to_end_with("/pullrequests/7/statuses")
```

</details>

### bb auth header

#### builds Bearer header when token present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bb_auth_header("abc123")).to_equal("Bearer abc123")
```

</details>

#### returns empty when token blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bb_auth_header("")).to_equal("")
```

</details>

### bb_build_create_pr_body

#### minimum body has title and source branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("My PR", "feat-x", "", [])
val parsed = json_parse(body)
expect(parsed != nil).to_equal(true)
expect(body).to_contain("\"title\": \"My PR\"")
expect(body).to_contain("\"source\":")
expect(body).to_contain("\"name\": \"feat-x\"")
```

</details>

#### omits destination when blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("T", "src", "", [])
expect(body).to_contain("\"source\":")
# destination should not appear
val has_dest = body.contains("\"destination\":")
expect(has_dest).to_equal(false)
```

</details>

#### includes destination when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("T", "src", "main", [])
expect(body).to_contain("\"destination\":")
expect(body).to_contain("\"name\": \"main\"")
```

</details>

#### includes reviewers as uuid objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("T", "src", "main", ["{u1}", "{u2}"])
expect(body).to_contain("\"reviewers\":")
expect(body).to_contain("\"uuid\": \"{u1}\"")
expect(body).to_contain("\"uuid\": \"{u2}\"")
```

</details>

#### produces parseable JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_create_pr_body("Add foo", "feat/foo", "develop", ["{abc-uuid}"])
val parsed = json_parse(body)
expect(parsed != nil).to_equal(true)
```

</details>

### bb_build_comment_body

#### general comment has no inline

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("Looks good", "", -1, -1)
expect(body).to_contain("\"raw\": \"Looks good\"")
expect(body).to_contain("\"markup\": \"markdown\"")
val has_inline = body.contains("\"inline\":")
expect(has_inline).to_equal(false)
```

</details>

#### inline comment includes path/from/to

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("Bug here", "src/foo.spl", -1, 42)
expect(body).to_contain("\"inline\":")
expect(body).to_contain("\"path\": \"src/foo.spl\"")
expect(body).to_contain("\"from\": null")
expect(body).to_contain("\"to\": 42")
```

</details>

#### inline with both line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("range", "x.spl", 10, 20)
expect(body).to_contain("\"from\": 10")
expect(body).to_contain("\"to\": 20")
```

</details>

#### escapes quotes in content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("she said \"hi\"", "", -1, -1)
expect(body).to_contain("\\\"hi\\\"")
```

</details>

#### produces parseable JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_comment_body("ok", "", -1, -1)
expect(json_parse(body) != nil).to_equal(true)
```

</details>

### bb_build_merge_body

#### squash strategy with close_source_branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_merge_body("squash", true, "")
expect(body).to_contain("\"merge_strategy\": \"squash\"")
expect(body).to_contain("\"close_source_branch\": true")
expect(body).to_contain("\"type\": \"pullrequest\"")
```

</details>

#### fast_forward strategy without close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_merge_body("fast_forward", false, "")
expect(body).to_contain("\"merge_strategy\": \"fast_forward\"")
expect(body).to_contain("\"close_source_branch\": false")
```

</details>

#### merge_commit with custom message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = bb_build_merge_body("merge_commit", true, "Release 1.0")
expect(body).to_contain("\"merge_strategy\": \"merge_commit\"")
expect(body).to_contain("\"message\": \"Release 1.0\"")
```

</details>

### bb_map_http_error

#### 401 maps to blocked-auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(401, "no token", BB_OP_GENERAL)
expect(e.kind).to_equal("auth_required")
expect(e.status_code).to_equal(401)
expect(e.message).to_contain("blocked-auth")
```

</details>

#### 403 on merge maps to blocked policy (api_error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(403, "branch restriction", BB_OP_MERGE)
expect(e.kind).to_equal("api_error")
expect(e.status_code).to_equal(403)
expect(e.message).to_contain("branch policy")
```

</details>

#### 403 on general maps to blocked-auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(403, "no scope", BB_OP_GENERAL)
expect(e.kind).to_equal("auth_required")
expect(e.status_code).to_equal(403)
```

</details>

#### 404 maps to not_found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(404, "", BB_OP_GENERAL)
expect(e.kind).to_equal("not_found")
expect(e.status_code).to_equal(404)
```

</details>

#### 409 maps to conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(409, "merge conflict", BB_OP_GENERAL)
expect(e.kind).to_equal("version_conflict")
expect(e.status_code).to_equal(409)
expect(e.message).to_contain("blocked-conflict")
```

</details>

#### 429 maps to network/rate-limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(429, "rate limit", BB_OP_GENERAL)
expect(e.kind).to_equal("network_error")
expect(e.status_code).to_equal(429)
```

</details>

#### 500 maps to api error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = bb_map_http_error(500, "boom", BB_OP_GENERAL)
expect(e.kind).to_equal("api_error")
expect(e.status_code).to_equal(500)
```

</details>

### bb_should_retry

#### non-429 does not retry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (retry, secs) = bb_should_retry(500, "")
expect(retry).to_equal(false)
expect(secs).to_equal(0)
```

</details>

#### 429 with Retry-After parses seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (retry, secs) = bb_should_retry(429, "30")
expect(retry).to_equal(true)
expect(secs).to_equal(30)
```

</details>

#### 429 without Retry-After defaults to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (retry, secs) = bb_should_retry(429, "")
expect(retry).to_equal(true)
expect(secs).to_equal(1)
```

</details>

### bb_eval_ready_to_merge

#### ready when OPEN + 1 approval + all SUCCESSFUL

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pr = json_parse(FIXTURE_PR_APPROVED_OPEN)
val st = json_parse(FIXTURE_STATUSES_OK)
val (ready, reason) = bb_eval_ready_to_merge(pr, st)
expect(ready).to_equal(true)
expect(reason).to_contain("ready")
```

</details>

#### not ready when no approvals

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pr = json_parse(FIXTURE_PR_PENDING)
val st = json_parse(FIXTURE_STATUSES_OK)
val (ready, reason) = bb_eval_ready_to_merge(pr, st)
expect(ready).to_equal(false)
expect(reason).to_contain("no approved reviewers")
```

</details>

#### not ready when PR not OPEN

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pr = json_parse(FIXTURE_PR_CLOSED)
val st = json_parse(FIXTURE_STATUSES_OK)
val (ready, reason) = bb_eval_ready_to_merge(pr, st)
expect(ready).to_equal(false)
expect(reason).to_contain("expected OPEN")
```

</details>

#### not ready when a status FAILED

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pr = json_parse(FIXTURE_PR_APPROVED_OPEN)
val st = json_parse(FIXTURE_STATUSES_FAIL)
val (ready, reason) = bb_eval_ready_to_merge(pr, st)
expect(ready).to_equal(false)
expect(reason).to_contain("FAILED")
```

</details>

#### not ready when no statuses found

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pr = json_parse(FIXTURE_PR_APPROVED_OPEN)
val st = json_parse(FIXTURE_STATUSES_EMPTY)
val (ready, reason) = bb_eval_ready_to_merge(pr, st)
expect(ready).to_equal(false)
expect(reason).to_contain("no commit statuses")
```

</details>

#### not ready when participants missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pr = json_parse("{\"state\": \"OPEN\"}")
val st = json_parse(FIXTURE_STATUSES_OK)
val (ready, reason) = bb_eval_ready_to_merge(pr, st)
expect(ready).to_equal(false)
expect(reason).to_contain("no participants")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_bitbucket_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bb URL builders
- bb auth header
- bb_build_create_pr_body
- bb_build_comment_body
- bb_build_merge_body
- bb_map_http_error
- bb_should_retry
- bb_eval_ready_to_merge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
