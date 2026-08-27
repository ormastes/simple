# Adapter Bitbucket Curl Live Specification

> Tests covering adapter_bitbucket_curl — live (skipped), adapter_bitbucket_curl — live read-only smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Bitbucket Curl Live Specification

## Scenarios

### adapter_bitbucket_curl — live (skipped)

#### skipped (no creds: set BB_WORKSPACE/BB_REPO/BB_TOKEN/BB_TEST_PR_ID)
### adapter_bitbucket_curl — live read-only smoke

#### get_pr returns success and id matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = BbCurlClient(
    base_url: "https://api.bitbucket.org/2.0",
    workspace: BB_WS,
    repo: BB_RP,
    token: BB_TK,
    curl_path: "curl"
)
val (ok, pr, _raw) = bbc_get_pr(client, BB_PR_ID)
expect(ok).to_equal(true)
expect(pr.id).to_equal(BB_PR_ID)
```

</details>

#### list_pr_comments succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = BbCurlClient(
    base_url: "https://api.bitbucket.org/2.0",
    workspace: BB_WS,
    repo: BB_RP,
    token: BB_TK,
    curl_path: "curl"
)
val (ok, _comments, _raw) = bbc_list_pr_comments(client, BB_PR_ID)
expect(ok).to_equal(true)
```

</details>

#### get_pr_statuses succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = BbCurlClient(
    base_url: "https://api.bitbucket.org/2.0",
    workspace: BB_WS,
    repo: BB_RP,
    token: BB_TK,
    curl_path: "curl"
)
val (ok, _statuses, _raw) = bbc_get_pr_statuses(client, BB_PR_ID)
expect(ok).to_equal(true)
```

</details>

#### check_ready_to_merge returns a (bool, reason) without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = BbCurlClient(
    base_url: "https://api.bitbucket.org/2.0",
    workspace: BB_WS,
    repo: BB_RP,
    token: BB_TK,
    curl_path: "curl"
)
val (_ready, reason) = bbc_check_ready_to_merge(client, BB_PR_ID)
expect(reason.len() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering adapter_bitbucket_curl — live (skipped), adapter_bitbucket_curl — live read-only smoke.
- adapter_bitbucket_curl — live (skipped)
- adapter_bitbucket_curl — live read-only smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b52d746aa9cc7df1d06a1d0edb91d854f33154c253a303be85feb2beeb709657`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b52d746aa9cc7df1d06a1d0edb91d854f33154c253a303be85feb2beeb709657`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b52d746aa9cc7df1d06a1d0edb91d854f33154c253a303be85feb2beeb709657`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl
mirror: doc/06_spec/03_system/e2e/adapter_bitbucket_curl_live_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/03_system/e2e/adapter_bitbucket_curl_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/e2e/adapter_bitbucket_curl_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl:66:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'skipped (no creds: set BB_WORKSPACE/BB_REPO/BB_TOKEN/BB_TEST_PR_ID)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'get_pr returns success and id matches' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl:87:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'list_pr_comments succeeds' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_bitbucket_curl_live_spec.spl:99:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'get_pr_statuses succeeds' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
