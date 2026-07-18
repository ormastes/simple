# Tooling Artifact Collector Specification

> <details>

<!-- sdn-diagram:id=tooling_artifact_collector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tooling_artifact_collector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tooling_artifact_collector_spec -> app
tooling_artifact_collector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tooling_artifact_collector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tooling Artifact Collector Specification

## Scenarios

### LLM dashboard tooling artifact collector

#### summarizes context and ponytail artifacts for a readable file

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_tooling_fixture("clean", "fn hello() -> text:\n    \"ok\"\n")
val panel = collect_llm_tooling_artifacts(path, "hello")

expect(panel.context_status).to_equal("ready")
expect(panel.context_lines).to_be_greater_than(0)
expect(panel.context_token_estimate).to_be_greater_than(0)
expect(panel.context_preview).to_contain("hello")
expect(panel.ponytail_status).to_equal("ok")
```

</details>

#### renders text without internal absence markers

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_tooling_fixture("smell", "interface FutureThing:\n    pass_todo\n")
val text = render_llm_tooling_artifacts_panel_text(collect_llm_tooling_artifacts(path, "FutureThing"))

expect(text).to_contain("LLM Tooling Artifacts")
expect(text).to_contain("context_status=ready")
expect(text).to_contain("ponytail_status=review")
expect_absence_marker_hidden(text)
```

</details>

#### renders missing files as explicit absence

- remove file if exists
- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _tooling_fixture_path("missing")
remove_file_if_exists(path)
val text = render_llm_tooling_artifacts_panel_text(collect_llm_tooling_artifacts(path, "missing"))

expect(text).to_contain("context_status=missing")
expect(text).to_contain("ponytail_status=missing")
expect(text).to_contain("ponytail_reason=source unavailable")
expect_absence_marker_hidden(text)
```

</details>

#### escapes html panel fields and preview

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_tooling_fixture("html", "fn danger() -> text:\n    \"<tag>&\"\n")
val html = render_llm_tooling_artifacts_panel_html(collect_llm_tooling_artifacts(path, "danger"))

expect(html).to_contain("llm-tooling-artifacts-panel")
expect(html).to_contain("&lt;tag&gt;&amp;")
expect(html.split("<tag>").len()).to_equal(1)
expect_absence_marker_hidden(html)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM dashboard tooling artifact collector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
