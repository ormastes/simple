# Itf Api Specification

> Tests covering _resolve_api_url, _build_api_headers, jira_api_base / confluence_api_base (--jira REST base selection).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Itf Api Specification

## Scenarios

### _resolve_api_url

#### prefixes a relative path with the base

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prefixes a relative path with the base
   - Expected: _resolve_api_url("/pages?limit=5", "https://x.atlassian.net/wiki/api/v2") equals `https://x.atlassian.net/wiki/api/v2/pages?limit=5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("prefixes a relative path with the base")
expect(_resolve_api_url("/pages?limit=5", "https://x.atlassian.net/wiki/api/v2")).to_equal("https://x.atlassian.net/wiki/api/v2/pages?limit=5")
```

</details>

#### leaves an absolute URL unchanged even when a base is available

- leaves an absolute URL unchanged even when a base is available
   - Expected: _resolve_api_url("https://other.example.com/thing", "https://x.atlassian.net/wiki/api/v2") equals `https://other.example.com/thing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves an absolute URL unchanged even when a base is available")
expect(_resolve_api_url("https://other.example.com/thing", "https://x.atlassian.net/wiki/api/v2")).to_equal("https://other.example.com/thing")
```

</details>

#### leaves a relative path unchanged when no base is configured

- leaves a relative path unchanged when no base is configured
   - Expected: _resolve_api_url("/pages", "") equals `/pages`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves a relative path unchanged when no base is configured")
expect(_resolve_api_url("/pages", "")).to_equal("/pages")
```

</details>

### _build_api_headers

#### always includes Accept: application/json

- always includes Accept: application/json
   - Expected: headers.len() equals `1`
   - Expected: headers[0] equals `Accept: application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("always includes Accept: application/json")
val headers = _build_api_headers("", "", false)
expect(headers.len()).to_equal(1)
expect(headers[0]).to_equal("Accept: application/json")
```

</details>

#### adds Authorization when auth is configured

- adds Authorization when auth is configured
   - Expected: headers contains `Authorization: Basic xyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("adds Authorization when auth is configured")
val headers = _build_api_headers("Basic xyz", "", false)
expect(headers.contains("Authorization: Basic xyz")).to_equal(true)
```

</details>

#### adds Content-Type when a body is present

- adds Content-Type when a body is present
   - Expected: headers contains `Content-Type: application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("adds Content-Type when a body is present")
val headers = _build_api_headers("", "", true)
expect(headers.contains("Content-Type: application/json")).to_equal(true)
```

</details>

#### attaches --header verbatim — the fix for the previously-dead flag

- attaches --header verbatim — the fix for the previously-dead flag
   - Expected: headers contains `X-Custom: value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("attaches --header verbatim — the fix for the previously-dead flag")
val headers = _build_api_headers("", "X-Custom: value", false)
expect(headers.contains("X-Custom: value")).to_equal(true)
```

</details>

#### combines all four when everything is set

- combines all four when everything is set
   - Expected: headers.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("combines all four when everything is set")
val headers = _build_api_headers("Basic xyz", "X-Custom: value", true)
expect(headers.len()).to_equal(4)
```

</details>

### jira_api_base / confluence_api_base (--jira REST base selection)

#### jira_api_base appends rest/api/3

- jira_api_base appends rest/api/3
   - Expected: jira_api_base(_config_with_jira_url("https://x.atlassian.net")) equals `https://x.atlassian.net/rest/api/3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira_api_base appends rest/api/3")
expect(jira_api_base(_config_with_jira_url("https://x.atlassian.net"))).to_equal("https://x.atlassian.net/rest/api/3")
```

</details>

#### jira_api_base handles a trailing slash

- jira_api_base handles a trailing slash
   - Expected: jira_api_base(_config_with_jira_url("https://x.atlassian.net/")) equals `https://x.atlassian.net/rest/api/3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira_api_base handles a trailing slash")
expect(jira_api_base(_config_with_jira_url("https://x.atlassian.net/"))).to_equal("https://x.atlassian.net/rest/api/3")
```

</details>

#### jira_api_base is empty when jira.url isn't configured

- jira_api_base is empty when jira.url isn't configured
   - Expected: jira_api_base(_config_with_jira_url("")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira_api_base is empty when jira.url isn't configured")
expect(jira_api_base(_config_with_jira_url(""))).to_equal("")
```

</details>

#### confluence_api_base still appends api/v2 (default, unchanged by --jira)

- confluence_api_base still appends api/v2 (default, unchanged by --jira)
   - Expected: confluence_api_base(_config_with_confluence_url("https://x.atlassian.net/wiki")) equals `https://x.atlassian.net/wiki/api/v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("confluence_api_base still appends api/v2 (default, unchanged by --jira)")
expect(confluence_api_base(_config_with_confluence_url("https://x.atlassian.net/wiki"))).to_equal("https://x.atlassian.net/wiki/api/v2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/itf_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering _resolve_api_url, _build_api_headers, jira_api_base / confluence_api_base (--jira REST base selection).
- _resolve_api_url
- _build_api_headers
- jira_api_base / confluence_api_base (--jira REST base selection)

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb1674c10c5d6d018476418a55aea4a5d0d1432b9882ade3298f79a585aa220e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb1674c10c5d6d018476418a55aea4a5d0d1432b9882ade3298f79a585aa220e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb1674c10c5d6d018476418a55aea4a5d0d1432b9882ade3298f79a585aa220e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/devhub/itf_api_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/itf_api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/itf_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/itf_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/itf_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/itf_api_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefixes a relative path with the base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/itf_api_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves an absolute URL unchanged even when a base is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/itf_api_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves a relative path unchanged when no base is configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
