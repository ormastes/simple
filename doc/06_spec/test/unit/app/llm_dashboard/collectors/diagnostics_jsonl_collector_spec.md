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
| 6 | 6 | 0 | 0 |

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

#### renders absence-safe diagnostics panel summary

- mkdir p
- remove file if exists
- write file
   - Expected: text does not contain `nil`
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
expect(text.contains("nil")).to_equal(false)
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

#### keeps missing diagnostics fields nil-free

- mkdir p
- remove file if exists
- write file
   - Expected: text does not contain `nil`
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
expect(text.contains("nil")).to_equal(false)
remove_file_if_exists(path)
```

</details>

#### keeps missing files nil-free

- remove file if exists
   - Expected: text does not contain `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = fixture_diag_path()
remove_file_if_exists(path)
val text = render_llm_diagnostics_panel_text(collect_llm_diagnostics_jsonl(path))
expect(text).to_contain("events=0")
expect(text).to_contain("last_event=none")
expect(text).to_contain("last_session=none")
expect(text.contains("nil")).to_equal(false)
```

</details>

#### escapes diagnostics field text in html

- mkdir p
- remove file if exists
- write file
   - Expected: html does not contain `<tag>`
   - Expected: html does not contain `nil`
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
expect(html.contains("<tag>")).to_equal(false)
expect(html.contains("nil")).to_equal(false)
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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
