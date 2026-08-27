# Github Release Specification

> Tests covering GitHub release helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Github Release Specification

## Scenarios

### GitHub release helpers

#### basename

#### returns the final path segment

- returns the final path segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns the final path segment")
expect basename("release/simple-bootstrap-1.0.0.spk") to_equal "simple-bootstrap-1.0.0.spk"
```

</details>

#### returns the original text when no slash exists

- returns the original text when no slash exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns the original text when no slash exists")
expect basename("artifact.txt") to_equal "artifact.txt"
```

</details>

#### strip_upload_url_template

#### removes github upload url templates

- removes github upload url templates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("removes github upload url templates")
val raw = "https://uploads.github.com/repos/org/repo/releases/1/assets{?name,label}"
expect strip_upload_url_template(raw) to_equal "https://uploads.github.com/repos/org/repo/releases/1/assets"
```

</details>

#### keeps plain urls unchanged

- keeps plain urls unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps plain urls unchanged")
val raw = "https://uploads.github.com/repos/org/repo/releases/1/assets"
expect strip_upload_url_template(raw) to_equal raw
```

</details>

#### guess_content_type

#### detects text checksum files

- detects text checksum files


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects text checksum files")
expect guess_content_type("SHA256SUMS.txt") to_equal "text/plain; charset=utf-8"
```

</details>

#### detects gzip-like bootstrap packages

- detects gzip-like bootstrap packages


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects gzip-like bootstrap packages")
expect guess_content_type("simple-bootstrap-1.0.0.spk") to_equal "application/gzip"
```

</details>

#### falls back to octet stream

- falls back to octet stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("falls back to octet stream")
expect guess_content_type("simple-binary") to_equal "application/octet-stream"
```

</details>

#### build_release_payload

#### includes required github release fields

- includes required github release fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes required github release fields")
val payload = build_release_payload("v1.2.3", "Simple Language v1.2.3", "notes", "", false, false)
expect payload to_contain "\"tag_name\": \"v1.2.3\""
expect payload to_contain "\"name\": \"Simple Language v1.2.3\""
expect payload to_contain "\"draft\": false"
```

</details>

#### adds target_commitish when provided

- adds target_commitish when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds target_commitish when provided")
val payload = build_release_payload("v1.2.3", "Simple", "notes", "abc123", false, true)
expect payload to_contain "\"target_commitish\": \"abc123\""
expect payload to_contain "\"prerelease\": true"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/release/github_release_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GitHub release helpers.
- GitHub release helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46515f063eb8e5f7eeb8dbeddcc7177d39eebde4192c2d70a7fae4f82b28eaa7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46515f063eb8e5f7eeb8dbeddcc7177d39eebde4192c2d70a7fae4f82b28eaa7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46515f063eb8e5f7eeb8dbeddcc7177d39eebde4192c2d70a7fae4f82b28eaa7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/release/github_release_spec.spl
mirror: doc/06_spec/02_integration/app/release/github_release_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/release/github_release_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/release/github_release_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/release/github_release_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the final path segment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/release/github_release_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the original text when no slash exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/release/github_release_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes github upload url templates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
