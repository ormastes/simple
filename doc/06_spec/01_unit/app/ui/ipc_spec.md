# Ipc Specification

> <details>

<!-- sdn-diagram:id=ipc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_spec -> common
ipc_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Specification

## Scenarios

### extract_json_field

#### extracts type field from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val result = extract_json_field(json, "type")
expect(result).to_equal("keypress")
```

</details>

#### extracts key field from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val result = extract_json_field(json, "key")
expect(result).to_equal("a")
```

</details>

#### returns empty string for missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val result = extract_json_field(json, "missing")
expect(result).to_equal("")
```

</details>

#### handles JSON with spaces around colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\": \"action\", \"name\": \"save\"}"
val result = extract_json_field(json, "name")
expect(result).to_equal("save")
```

</details>

#### returns empty string for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_json_field("", "type")
expect(result).to_equal("")
```

</details>

### parse_ipc_message

#### parses keypress message into UIEvent.KeyPress

1. UIEvent KeyPress
   - Expected: key equals `q`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"keypress\",\"key\":\"q\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
match event:
    UIEvent.KeyPress(key):
        expect(key).to_equal("q")
    _:
        expect(false).to_equal(true)
```

</details>

#### parses quit message into UIEvent.Quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"quit\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
```

</details>

#### returns nil for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("")
expect(event == nil).to_equal(true)
```

</details>

#### returns nil for unrecognized message type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"unknown\",\"data\":\"test\"}"
val event = parse_ipc_message(json)
expect(event == nil).to_equal(true)
```

</details>

#### parses action message

1. UIEvent Action
   - Expected: name equals `open_file`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"action\",\"name\":\"open_file\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
match event:
    UIEvent.Action(name):
        expect(name).to_equal("open_file")
    _:
        expect(false).to_equal(true)
```

</details>

#### parses resize message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"resize\",\"width\":\"120\",\"height\":\"40\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
```

</details>

### build_ipc_render

#### wraps html in JSON with type render

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<div>Hello</div>"
val result = build_ipc_render(html)
expect(result).to_contain("\"type\":\"render\"")
```

</details>

#### includes html content in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<p>Test</p>"
val result = build_ipc_render(html)
expect(result).to_contain("Test")
```

</details>

#### produces valid JSON structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<span>Hi</span>"
val result = build_ipc_render(html)
expect(result).to_contain("{")
expect(result).to_contain("}")
```

</details>

### escape_ipc_json

#### escapes double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_ipc_json("say \"hello\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes backslashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_ipc_json("path\\to\\file")
expect(result).to_contain("\\\\")
```

</details>

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_ipc_json("line1\nline2")
expect(result).to_contain("\\n")
```

</details>

#### passes plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_ipc_json("hello world")
expect(result).to_equal("hello world")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_ipc_json("")
expect(result).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ipc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extract_json_field
- parse_ipc_message
- build_ipc_render
- escape_ipc_json

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
