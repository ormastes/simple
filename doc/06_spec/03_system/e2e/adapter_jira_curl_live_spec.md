# Adapter Jira Curl Live Specification

> Tests covering adapter_jira_curl - live Jira Cloud.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Jira Curl Live Specification

## Scenarios

### adapter_jira_curl - live Jira Cloud

#### skipped (no creds: set JIRA_URL, JIRA_USER, JIRA_TOKEN)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(_have_creds).to_equal(false)
```

</details>

#### search returns >= 0 issues for the configured project

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = JiraClient(
    base_url: _jira_url,
    email: _jira_user,
    api_token: _jira_token,
    curl_path: "curl",
)
val (ok, issues, _raw) = jira_curl_search(client, _project_jql, "summary,status", 5)
expect(ok).to_equal(true)
expect(issues.len() >= 0).to_equal(true)
```

</details>

#### view of the first search hit succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = JiraClient(
    base_url: _jira_url,
    email: _jira_user,
    api_token: _jira_token,
    curl_path: "curl",
)
val (ok, issues, _raw) = jira_curl_search(client, _project_jql, "summary", 1)
expect(ok).to_equal(true)
if issues.len() > 0:
    val (vok, issue, _vraw) = jira_curl_view_issue(client, issues[0].key)
    expect(vok).to_equal(true)
    expect(issue.key).to_equal(issues[0].key)
else:
    # Empty project is still a passing live smoke - the search
    # itself returned 200; we have nothing to view.
    expect(issues.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/e2e/adapter_jira_curl_live_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering adapter_jira_curl - live Jira Cloud.
- adapter_jira_curl - live Jira Cloud

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `3ce42bf35e45c516dcf40f1fb657ae21a24503fc2b5825c8c39b1ad6c6937029`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ce42bf35e45c516dcf40f1fb657ae21a24503fc2b5825c8c39b1ad6c6937029`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ce42bf35e45c516dcf40f1fb657ae21a24503fc2b5825c8c39b1ad6c6937029`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/e2e/adapter_jira_curl_live_spec.spl
mirror: doc/06_spec/03_system/e2e/adapter_jira_curl_live_spec.md (current)
findings: 8 blockers: 0
  narrative=80 structure=70 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/e2e/adapter_jira_curl_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/e2e/adapter_jira_curl_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/e2e/adapter_jira_curl_live_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/e2e/adapter_jira_curl_live_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/e2e/adapter_jira_curl_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/e2e/adapter_jira_curl_live_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'skipped (no creds: set JIRA_URL, JIRA_USER, JIRA_TOKEN)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_jira_curl_live_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'search returns >= 0 issues for the configured project' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_jira_curl_live_spec.spl:55:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'view of the first search hit succeeds' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
