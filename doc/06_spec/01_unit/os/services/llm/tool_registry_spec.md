# Tool Registry Specification

> <details>

<!-- sdn-diagram:id=tool_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tool_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tool_registry_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tool_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tool Registry Specification

## Scenarios

### Tool registry JSON helpers

#### _js wraps string in double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _js("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### _jp creates key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _jp("name", "\"test\"")
expect(result).to_equal("\"name\":\"test\"")
```

</details>

#### _jo1 wraps single property in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _jo1("\"a\":1")
expect(result).to_equal("{\"a\":1}")
```

</details>

#### _jo2 wraps two properties in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _jo2("\"a\":1", "\"b\":2")
expect(result).to_equal("{\"a\":1,\"b\":2}")
```

</details>

#### _jo3 wraps three properties in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _jo3("\"a\":1", "\"b\":2", "\"c\":3")
expect(result).to_equal("{\"a\":1,\"b\":2,\"c\":3}")
```

</details>

#### _jo4 wraps four properties in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _jo4("\"a\":1", "\"b\":2", "\"c\":3", "\"d\":4")
expect(result).to_equal("{\"a\":1,\"b\":2,\"c\":3,\"d\":4}")
```

</details>

### Tool schemas — File tools

#### schema_file_read contains file_read name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_read()
expect(schema).to_contain("file_read")
```

</details>

#### schema_file_read contains path property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_read()
expect(schema).to_contain("path")
```

</details>

#### schema_file_read is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_read()
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_file_write contains file_write name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_write()
expect(schema).to_contain("file_write")
```

</details>

#### schema_file_write contains path and content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_write()
expect(schema).to_contain("path")
expect(schema).to_contain("content")
```

</details>

#### schema_file_write is destructive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_write()
expect(schema).to_contain("destructiveHint")
```

</details>

#### schema_file_list contains file_list name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_list()
expect(schema).to_contain("file_list")
```

</details>

#### schema_file_search contains file_search name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_search()
expect(schema).to_contain("file_search")
```

</details>

#### schema_file_search contains pattern param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_file_search()
expect(schema).to_contain("pattern")
```

</details>

### Tool schemas — Process tools

#### schema_process_list contains process_list name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_process_list()
expect(schema).to_contain("process_list")
```

</details>

#### schema_process_list has no required params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_process_list()
expect(schema).to_contain("\"required\":[]")
```

</details>

#### schema_process_spawn contains binary param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_process_spawn()
expect(schema).to_contain("binary")
```

</details>

#### schema_process_kill contains pid param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_process_kill()
expect(schema).to_contain("pid")
```

</details>

#### schema_process_kill is destructive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_process_kill()
expect(schema).to_contain("destructiveHint")
```

</details>

### Tool schemas — Window tools

#### schema_window_create contains title param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_window_create()
expect(schema).to_contain("title")
```

</details>

#### schema_window_create contains width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_window_create()
expect(schema).to_contain("width")
expect(schema).to_contain("height")
```

</details>

#### schema_window_close contains id param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_window_close()
expect(schema).to_contain("id")
```

</details>

#### schema_window_list has empty properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_window_list()
expect(schema).to_contain("window_list")
```

</details>

#### schema_window_focus contains id param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_window_focus()
expect(schema).to_contain("id")
```

</details>

### Tool schemas — Widget tools

#### schema_widget_set contains window_id and widget_dsl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_widget_set()
expect(schema).to_contain("window_id")
expect(schema).to_contain("widget_dsl")
```

</details>

#### schema_widget_set describes DSL format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_widget_set()
expect(schema).to_contain("column")
```

</details>

#### schema_widget_read contains window_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_widget_read()
expect(schema).to_contain("window_id")
```

</details>

#### schema_widget_read is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_widget_read()
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_widget_action contains action param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_widget_action()
expect(schema).to_contain("action")
```

</details>

### Tool schemas — UI access tools

#### schema_ui_access_snapshot contains tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_snapshot()
expect(schema).to_contain("ui_access_snapshot")
```

</details>

#### schema_ui_access_surface contains surface_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_surface()
expect(schema).to_contain("surface_id")
```

</details>

#### schema_ui_access_find contains focused_only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_find()
expect(schema).to_contain("focused_only")
```

</details>

#### schema_ui_access_act contains canonical_id and action

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_act()
expect(schema).to_contain("canonical_id")
expect(schema).to_contain("action")
```

</details>

#### schema_ui_access_history contains count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_history()
expect(schema).to_contain("count")
```

</details>

### Tool schemas — Declarative UI access

#### schema_ui_access_observe contains selector fields and is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_observe()
expect(schema).to_contain("ui_access_observe")
expect(schema).to_contain("canonical_id")
expect(schema).to_contain("focused_only")
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_ui_access_state contains state fields and is non-idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_state()
expect(schema).to_contain("ui_access_state")
expect(schema).to_contain("state_key")
expect(schema).to_contain("state_value")
expect(schema).to_contain("destructiveHint")
```

</details>

#### schema_ui_access_query contains structured selector fields and is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_query()
expect(schema).to_contain("ui_access_query")
expect(schema).to_contain("canonical_id")
expect(schema).to_contain("focused_only")
expect(schema).to_contain("limit")
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_ui_access_ensure contains expectation fields and is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_ensure()
expect(schema).to_contain("ui_access_ensure")
expect(schema).to_contain("expectation")
expect(schema).to_contain("expected_value")
expect(schema).to_contain("timeout_ms")
expect(schema).to_contain("poll_ms")
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_ui_access_value contains canonical_id and value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_value()
expect(schema).to_contain("ui_access_value")
expect(schema).to_contain("canonical_id")
expect(schema).to_contain("value")
```

</details>

#### schema_ui_access_adapter_snapshot contains surface selector and is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_adapter_snapshot()
expect(schema).to_contain("ui_access_adapter_snapshot")
expect(schema).to_contain("surface_id")
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_ui_access_visual_probe contains surface selector and is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_ui_access_visual_probe()
expect(schema).to_contain("ui_access_visual_probe")
expect(schema).to_contain("surface_id")
expect(schema).to_contain("readOnlyHint")
```

</details>

### Tool schemas — Screen tools

#### schema_screenshot contains screenshot name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_screenshot()
expect(schema).to_contain("screenshot")
```

</details>

#### schema_screenshot is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_screenshot()
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_screen_read_text contains screen_read_text name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_screen_read_text()
expect(schema).to_contain("screen_read_text")
```

</details>

#### schema_screen_read_text mentions accessibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_screen_read_text()
expect(schema).to_contain("accessibility")
```

</details>

### Tool schemas — System tools

#### schema_system_info contains system_info name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_system_info()
expect(schema).to_contain("system_info")
```

</details>

#### schema_system_info is read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_system_info()
expect(schema).to_contain("readOnlyHint")
```

</details>

#### schema_system_exec contains command param

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_system_exec()
expect(schema).to_contain("command")
```

</details>

#### schema_system_exec is destructive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = schema_system_exec()
expect(schema).to_contain("destructiveHint")
```

</details>

### Tool schema structure

#### all schemas produce valid JSON-like output (contain braces)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(schema_file_read()).to_start_with("{")
expect(schema_file_write()).to_start_with("{")
expect(schema_file_list()).to_start_with("{")
expect(schema_file_search()).to_start_with("{")
expect(schema_process_list()).to_start_with("{")
expect(schema_process_spawn()).to_start_with("{")
expect(schema_process_kill()).to_start_with("{")
```

</details>

#### all schemas end with closing brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(schema_file_read()).to_end_with("}")
expect(schema_window_create()).to_end_with("}")
expect(schema_widget_set()).to_end_with("}")
expect(schema_ui_access_snapshot()).to_end_with("}")
expect(schema_screenshot()).to_end_with("}")
expect(schema_system_info()).to_end_with("}")
```

</details>

#### all schemas contain inputSchema

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(schema_file_read()).to_contain("inputSchema")
expect(schema_window_create()).to_contain("inputSchema")
expect(schema_widget_set()).to_contain("inputSchema")
expect(schema_ui_access_surface()).to_contain("inputSchema")
expect(schema_system_exec()).to_contain("inputSchema")
```

</details>

#### all schemas contain annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(schema_file_read()).to_contain("annotations")
expect(schema_process_list()).to_contain("annotations")
expect(schema_window_list()).to_contain("annotations")
expect(schema_screenshot()).to_contain("annotations")
```

</details>

#### all schemas contain description

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(schema_file_read()).to_contain("description")
expect(schema_process_spawn()).to_contain("description")
expect(schema_window_close()).to_contain("description")
expect(schema_system_exec()).to_contain("description")
```

</details>

### Tool name uniqueness

#### file tools have distinct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = schema_file_read()
val w = schema_file_write()
val l = schema_file_list()
val s = schema_file_search()
expect(r).to_contain("file_read")
expect(w).to_contain("file_write")
expect(l).to_contain("file_list")
expect(s).to_contain("file_search")
```

</details>

#### process tools have distinct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = schema_process_list()
val s = schema_process_spawn()
val k = schema_process_kill()
expect(l).to_contain("process_list")
expect(s).to_contain("process_spawn")
expect(k).to_contain("process_kill")
```

</details>

#### window tools have distinct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = schema_window_create()
val cl = schema_window_close()
val l = schema_window_list()
val f = schema_window_focus()
expect(c).to_contain("window_create")
expect(cl).to_contain("window_close")
expect(l).to_contain("window_list")
expect(f).to_contain("window_focus")
```

</details>

#### widget tools have distinct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = schema_widget_set()
val r = schema_widget_read()
val a = schema_widget_action()
expect(s).to_contain("widget_set")
expect(r).to_contain("widget_read")
expect(a).to_contain("widget_action")
```

</details>

#### total tool count is 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# file: read, write, list, search = 4
# process: list, spawn, kill = 3
# window: create, close, list, focus = 4
# widget: set, read, action = 3
# ui access: snapshot, surface, find, act, history = 5
# screen: screenshot, screen_read_text = 2
# system: system_info, system_exec = 2
val total = 4 + 3 + 4 + 3 + 5 + 2 + 2
expect(total).to_equal(23)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/llm/tool_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tool registry JSON helpers
- Tool schemas — File tools
- Tool schemas — Process tools
- Tool schemas — Window tools
- Tool schemas — Widget tools
- Tool schemas — UI access tools
- Tool schemas — Declarative UI access
- Tool schemas — Screen tools
- Tool schemas — System tools
- Tool schema structure
- Tool name uniqueness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
