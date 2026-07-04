# Diagnostics Jsonl Collector Specification

> <details>

<!-- sdn-diagram:id=diagnostics_jsonl_collector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagnostics_jsonl_collector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagnostics_jsonl_collector_spec -> app
diagnostics_jsonl_collector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagnostics_jsonl_collector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostics Jsonl Collector Specification

## Scenarios

### LLM diagnostics dashboard JSONL collector

#### summarizes hook JSONL for dashboard panels

- mkdir p
- remove file if exists
- write file
   - Expected: panel.event_count equals `4`
   - Expected: panel.session_count equals `2`
   - Expected: panel.tool_event_count equals `2`
   - Expected: panel.last_session_id equals `sid-b`
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, fixture_diag_jsonl())
val panel = collect_llm_diagnostics_jsonl(path)
expect(panel.event_count).to_equal(4)
expect(panel.session_count).to_equal(2)
expect(panel.tool_event_count).to_equal(2)
expect(panel.last_session_id).to_equal("sid-b")
remove_file_if_exists(path)
```

</details>

#### summarizes vLLM runtime evidence for dashboard panels

- mkdir p
- remove file if exists
- write file
   - Expected: panel.event_count equals `2`
   - Expected: panel.vllm_event_count equals `2`
   - Expected: panel.last_vllm_status equals `ready`
   - Expected: panel.last_vllm_reason equals `models_endpoint_ready`
- expect absence marker hidden
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, fixture_vllm_jsonl())
val panel = collect_llm_diagnostics_jsonl(path)
expect(panel.event_count).to_equal(2)
expect(panel.vllm_event_count).to_equal(2)
expect(panel.last_vllm_status).to_equal("ready")
expect(panel.last_vllm_reason).to_equal("models_endpoint_ready")
val text = render_llm_diagnostics_panel_text(panel)
expect(text).to_contain("vllm_events=2")
expect(text).to_contain("vllm_status=ready")
expect(text).to_contain("vllm_reason=models_endpoint_ready")
expect_absence_marker_hidden(text)
remove_file_if_exists(path)
```

</details>

#### renders absence-safe diagnostics panel summary

- mkdir p
- remove file if exists
- write file
- expect absence marker hidden
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, fixture_diag_jsonl())
val text = render_llm_diagnostics_panel_text(collect_llm_diagnostics_jsonl(path))
expect(text).to_contain("LLM Diagnostics")
expect(text).to_contain("events=4")
expect_absence_marker_hidden(text)
remove_file_if_exists(path)
```

</details>

#### uses nested hook data fields from real hook payloads

- mkdir p
- remove file if exists
- write file
   - Expected: panel.event_count equals `2`
   - Expected: panel.session_count equals `1`
   - Expected: panel.tool_event_count equals `1`
   - Expected: panel.last_event equals `PreToolUse`
   - Expected: panel.last_session_id equals `sid-nested`
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, fixture_nested_diag_jsonl())
val panel = collect_llm_diagnostics_jsonl(path)
expect(panel.event_count).to_equal(2)
expect(panel.session_count).to_equal(1)
expect(panel.tool_event_count).to_equal(1)
expect(panel.last_event).to_equal("PreToolUse")
expect(panel.last_session_id).to_equal("sid-nested")
remove_file_if_exists(path)
```

</details>

#### keeps missing diagnostics fields absence-marker-free

- mkdir p
- remove file if exists
- write file
- expect absence marker hidden
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, fixture_missing_fields_jsonl())
val text = render_llm_diagnostics_panel_text(collect_llm_diagnostics_jsonl(path))
expect(text).to_contain("events=2")
expect(text).to_contain("last_event=PostToolUse")
expect(text).to_contain("last_session=none")
expect_absence_marker_hidden(text)
remove_file_if_exists(path)
```

</details>

#### keeps missing files absence-marker-free

- remove file if exists
- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
remove_file_if_exists(path)
val text = render_llm_diagnostics_panel_text(collect_llm_diagnostics_jsonl(path))
expect(text).to_contain("events=0")
expect(text).to_contain("last_event=none")
expect(text).to_contain("last_session=none")
expect(text).to_contain("vllm_status=none")
expect_absence_marker_hidden(text)
```

</details>

#### escapes diagnostics field text in html

- mkdir p
- remove file if exists
- write file
   - Expected: html.split("<tag>").len() equals `1`
- expect absence marker hidden
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, "{\"event\":\"PreToolUse<tag>\",\"sid\":\"sid&\"}\n")
val html = render_llm_diagnostics_panel_html(collect_llm_diagnostics_jsonl(path))
expect(html).to_contain("PreToolUse&lt;tag&gt;")
expect(html).to_contain("sid&amp;")
expect(html.split("<tag>").len()).to_equal(1)
expect_absence_marker_hidden(html)
remove_file_if_exists(path)
```

</details>

#### escapes vLLM status fields in html

- mkdir p
- remove file if exists
- write file
   - Expected: html.split("ready<tag>").len() equals `1`
- expect absence marker hidden
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, "{\"event\":\"llm_runtime_vllm_models_probe\",\"status\":\"ready<tag>\",\"reason\":\"models&endpoint\"}\n")
val html = render_llm_diagnostics_panel_html(collect_llm_diagnostics_jsonl(path))
expect(html).to_contain("vllm_events=1")
expect(html).to_contain("ready&lt;tag&gt;")
expect(html).to_contain("models&amp;endpoint")
expect(html.split("ready<tag>").len()).to_equal(1)
expect_absence_marker_hidden(html)
remove_file_if_exists(path)
```

</details>

#### decodes escaped JSONL string fields before dashboard rendering

- mkdir p
- remove file if exists
- write file
   - Expected: panel.vllm_event_count equals `1`
   - Expected: panel.last_vllm_status equals `ready"quoted`
   - Expected: panel.last_vllm_reason equals `models\\endpoint`
- expect absence marker hidden
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, "{\"event\":\"llm_runtime_vllm_models_probe\",\"status\":\"ready\\\"quoted\",\"reason\":\"models\\\\endpoint\"}\n")
val panel = collect_llm_diagnostics_jsonl(path)
expect(panel.vllm_event_count).to_equal(1)
expect(panel.last_vllm_status).to_equal("ready\"quoted")
expect(panel.last_vllm_reason).to_equal("models\\endpoint")
val html = render_llm_diagnostics_panel_html(panel)
expect(html).to_contain("ready&quot;quoted")
expect_absence_marker_hidden(html)
remove_file_if_exists(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/collectors/diagnostics_jsonl_collector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM diagnostics dashboard JSONL collector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
