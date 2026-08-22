# github_release_spec

> Verifies the github release behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# github_release_spec

Verifies the github release behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/release/github_release_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the github release behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### GitHub release helpers

#### basename

#### returns the final path segment

- Verify: returns the final path segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: returns the final path segment")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect basename("release/simple-bootstrap-1.0.0.spk") to_equal "simple-bootstrap-1.0.0.spk"
```

</details>

#### returns the original text when no slash exists

- Verify: returns the original text when no slash exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: returns the original text when no slash exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect basename("artifact.txt") to_equal "artifact.txt"
```

</details>

#### strip_upload_url_template

#### removes github upload url templates

- Verify: removes github upload url templates


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: removes github upload url templates")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val raw = "https://uploads.github.com/repos/org/repo/releases/1/assets{?name,label}"
expect strip_upload_url_template(raw) to_equal "https://uploads.github.com/repos/org/repo/releases/1/assets"
```

</details>

#### keeps plain urls unchanged

- Verify: keeps plain urls unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: keeps plain urls unchanged")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val raw = "https://uploads.github.com/repos/org/repo/releases/1/assets"
expect strip_upload_url_template(raw) to_equal raw
```

</details>

#### guess_content_type

#### detects text checksum files

- Verify: detects text checksum files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: detects text checksum files")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect guess_content_type("SHA256SUMS.txt") to_equal "text/plain; charset=utf-8"
```

</details>

#### detects gzip-like bootstrap packages

- Verify: detects gzip-like bootstrap packages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: detects gzip-like bootstrap packages")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect guess_content_type("simple-bootstrap-1.0.0.spk") to_equal "application/gzip"
```

</details>

#### falls back to octet stream

- Verify: falls back to octet stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: falls back to octet stream")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect guess_content_type("simple-binary") to_equal "application/octet-stream"
```

</details>

#### build_release_payload

#### includes required github release fields

- Verify: includes required github release fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: includes required github release fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val payload = build_release_payload("v1.2.3", "Simple Language v1.2.3", "notes", "", false, false)
expect payload to_contain "\"tag_name\": \"v1.2.3\""
expect payload to_contain "\"name\": \"Simple Language v1.2.3\""
expect payload to_contain "\"draft\": false"
```

</details>

#### adds target_commitish when provided

- Verify: adds target_commitish when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-RELEASE_GITHUB_RELEASE-001
step("Verify: adds target_commitish when provided")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val payload = build_release_payload("v1.2.3", "Simple", "notes", "abc123", false, true)
expect payload to_contain "\"target_commitish\": \"abc123\""
expect payload to_contain "\"prerelease\": true"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9906a0f3b8a349917b2cdf4c9496fe8a8ae211c1cfa9055332ada51d41e1d0f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9906a0f3b8a349917b2cdf4c9496fe8a8ae211c1cfa9055332ada51d41e1d0f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9906a0f3b8a349917b2cdf4c9496fe8a8ae211c1cfa9055332ada51d41e1d0f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/release/github_release_spec.spl
mirror: doc/06_spec/02_integration/app/release/github_release_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/release/github_release_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/release/github_release_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/release/github_release_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
