# Canonical Evidence Layout Specification

> Documents the canonical evidence layout used by `spipe-docgen` auto-discovery. Screenshots live under `doc/06_spec/image/<spec-relative-path>/` and non-image artifacts live under `build/test-artifacts/<spec-relative-path>/`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canonical Evidence Layout Specification

Documents the canonical evidence layout used by `spipe-docgen` auto-discovery. Screenshots live under `doc/06_spec/image/<spec-relative-path>/` and non-image artifacts live under `build/test-artifacts/<spec-relative-path>/`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EVIDENCE-001 |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/tooling/evidence_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Documents the canonical evidence layout used by `spipe-docgen` auto-discovery.
Screenshots live under `doc/06_spec/image/<spec-relative-path>/` and non-image
artifacts live under `build/test-artifacts/<spec-relative-path>/`.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Screenshot root | `doc/06_spec/image` |
| Artifact root | `build/test-artifacts` |
| Spec-relative path | Path derived from `test/.../*_spec.spl` without suffix |

## Behavior

- `doc/06_spec/image/<spec-relative-path>/` is the canonical screenshot tree
- `build/test-artifacts/<spec-relative-path>/` is the canonical non-image evidence tree
- Evidence paths are grouped by spec-relative directory, not by tool name
- Generated docs can auto-discover these paths when docblock metadata is absent

## Scenarios

### Canonical evidence layout

#### when mapping spec paths to evidence roots

#### uses doc/06_spec/image for screenshots

- uses doc/06_spec/image for screenshots
   - Expected: full_path equals `doc/06_spec/image/app/web_dashboard/tmux_rest_api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses doc/06_spec/image for screenshots")
val full_path = screenshot_dir_for_spec("test/feature/app/web_dashboard/tmux_rest_api_spec.spl")
expect(full_path).to_equal("doc/06_spec/image/app/web_dashboard/tmux_rest_api")
```

</details>

#### uses build/test-artifacts for logs and text artifacts

- uses build/test-artifacts for logs and text artifacts
   - Expected: full_path equals `build/test-artifacts/app/web_dashboard/tmux_rest_api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses build/test-artifacts for logs and text artifacts")
val full_path = artifact_dir_for_spec("test/feature/app/web_dashboard/tmux_rest_api_spec.spl")
expect(full_path).to_equal("build/test-artifacts/app/web_dashboard/tmux_rest_api")
```

</details>

#### keeps evidence grouped by spec-relative path

- keeps evidence grouped by spec-relative path
   - Expected: screenshot_path contains `app/web_dashboard/tmux_rest_api`
   - Expected: artifact_path contains `app/web_dashboard/tmux_rest_api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps evidence grouped by spec-relative path")
val screenshot_path = "{screenshot_dir_for_spec(\"test/feature/app/web_dashboard/tmux_rest_api_spec.spl\")}/after.png"
val artifact_path = "{artifact_dir_for_spec(\"test/feature/app/web_dashboard/tmux_rest_api_spec.spl\")}/run.log"
expect(screenshot_path.contains("app/web_dashboard/tmux_rest_api")).to_equal(true)
expect(artifact_path.contains("app/web_dashboard/tmux_rest_api")).to_equal(true)
```

</details>

#### strips the test suffix from the final path segment

- strips the test suffix from the final path segment
   - Expected: spec_relative_path("test/unit/app/tooling/command_dispatch_spec.spl") equals `unit/app/tooling/command_dispatch`
   - Expected: spec_relative_path("test/unit/app/tooling/runner_test.spl") equals `unit/app/tooling/runner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips the test suffix from the final path segment")
expect(spec_relative_path("test/unit/app/tooling/command_dispatch_spec.spl")).to_equal("unit/app/tooling/command_dispatch")
expect(spec_relative_path("test/unit/app/tooling/runner_test.spl")).to_equal("unit/app/tooling/runner")
```

</details>

#### classifies evidence by its canonical extension

- classifies evidence by its canonical extension
   - Expected: classify_evidence("doc/06_spec/image/app/demo/after.png") equals `screenshot`
   - Expected: classify_evidence("build/test-artifacts/app/demo/transcript.ansi") equals `tui`
   - Expected: classify_evidence("build/test-artifacts/app/demo/run.log") equals `log`
   - Expected: classify_evidence("build/test-artifacts/app/demo/result.json") equals `artifact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies evidence by its canonical extension")
expect(classify_evidence("doc/06_spec/image/app/demo/after.png")).to_equal("screenshot")
expect(classify_evidence("build/test-artifacts/app/demo/transcript.ansi")).to_equal("tui")
expect(classify_evidence("build/test-artifacts/app/demo/run.log")).to_equal("log")
expect(classify_evidence("build/test-artifacts/app/demo/result.json")).to_equal("artifact")
```

</details>

#### keeps stdlib test roots aligned with the same relative layout

- keeps stdlib test roots aligned with the same relative layout
   - Expected: screenshot_dir_for_spec("simple/std_lib/test/spec/screenshot_ffi_spec.spl") equals `doc/06_spec/image/spec/screenshot_ffi`
   - Expected: artifact_dir_for_spec("simple/std_lib/test/spec/screenshot_ffi_spec.spl") equals `build/test-artifacts/spec/screenshot_ffi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps stdlib test roots aligned with the same relative layout")
expect(screenshot_dir_for_spec("simple/std_lib/test/spec/screenshot_ffi_spec.spl")).to_equal("doc/06_spec/image/spec/screenshot_ffi")
expect(artifact_dir_for_spec("simple/std_lib/test/spec/screenshot_ffi_spec.spl")).to_equal("build/test-artifacts/spec/screenshot_ffi")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1f7aeb0f16c135a6e898beb5ab827fdd52a03b76e3820f52a91ef25fa9822f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1f7aeb0f16c135a6e898beb5ab827fdd52a03b76e3820f52a91ef25fa9822f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1f7aeb0f16c135a6e898beb5ab827fdd52a03b76e3820f52a91ef25fa9822f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/evidence_layout_spec.spl
mirror: doc/06_spec/unit/app/tooling/evidence_layout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/evidence_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/evidence_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/evidence_layout_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses doc/06_spec/image for screenshots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/evidence_layout_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses build/test-artifacts for logs and text artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/evidence_layout_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps evidence grouped by spec-relative path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
