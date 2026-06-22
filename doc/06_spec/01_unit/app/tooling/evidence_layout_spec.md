# Canonical Evidence Layout Specification

> Documents the canonical evidence layout used by `spipe-docgen` auto-discovery. Screenshots live under `doc/06_spec/image/<spec-relative-path>/` and non-image artifacts live under `build/test-artifacts/<spec-relative-path>/`.

<!-- sdn-diagram:id=evidence_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=evidence_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

evidence_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=evidence_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/app/tooling/evidence_layout_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_path = screenshot_dir_for_spec("test/feature/app/web_dashboard/tmux_rest_api_spec.spl")
expect(full_path).to_equal("doc/06_spec/image/app/web_dashboard/tmux_rest_api")
```

</details>

#### uses build/test-artifacts for logs and text artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_path = artifact_dir_for_spec("test/feature/app/web_dashboard/tmux_rest_api_spec.spl")
expect(full_path).to_equal("build/test-artifacts/app/web_dashboard/tmux_rest_api")
```

</details>

#### keeps evidence grouped by spec-relative path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val screenshot_path = "{screenshot_dir_for_spec(\"test/feature/app/web_dashboard/tmux_rest_api_spec.spl\")}/after.png"
val artifact_path = "{artifact_dir_for_spec(\"test/feature/app/web_dashboard/tmux_rest_api_spec.spl\")}/run.log"
expect(screenshot_path.contains("app/web_dashboard/tmux_rest_api")).to_equal(true)
expect(artifact_path.contains("app/web_dashboard/tmux_rest_api")).to_equal(true)
```

</details>

#### strips the test suffix from the final path segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(spec_relative_path("test/unit/app/tooling/command_dispatch_spec.spl")).to_equal("unit/app/tooling/command_dispatch")
expect(spec_relative_path("test/unit/app/tooling/runner_test.spl")).to_equal("unit/app/tooling/runner")
```

</details>

#### classifies evidence by its canonical extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(classify_evidence("doc/06_spec/image/app/demo/after.png")).to_equal("screenshot")
expect(classify_evidence("build/test-artifacts/app/demo/transcript.ansi")).to_equal("tui")
expect(classify_evidence("build/test-artifacts/app/demo/run.log")).to_equal("log")
expect(classify_evidence("build/test-artifacts/app/demo/result.json")).to_equal("artifact")
```

</details>

#### keeps stdlib test roots aligned with the same relative layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
