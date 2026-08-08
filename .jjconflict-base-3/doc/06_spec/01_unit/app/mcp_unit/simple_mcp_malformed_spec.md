# Simple Mcp Malformed Specification

> <details>

<!-- sdn-diagram:id=simple_mcp_malformed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_mcp_malformed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_mcp_malformed_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_mcp_malformed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Mcp Malformed Specification

## Scenarios

### Simple Mcp Malformed

#### keeps JSON-lines malformed input isolated from stdout bindings

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = protocol_source()

expect(src).to_contain("fn protocol_read_message(state: ProtocolState) -> text:")
expect(src).to_contain("if line.starts_with(\"{\"):")
expect(src).to_contain("state.use_json_lines = true")
expect(src).to_contain("return line")
expect(src).to_contain("extern fn print_raw(s: text) -> i64")
```

</details>

#### keeps content-length parsing separate from body reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = protocol_source()

expect(src).to_contain("line.starts_with(\"Content-Length:\")")
expect(src).to_contain("content_length = int(len_str)")
expect(src).to_contain("if content_length <= 0:")
expect(src).to_contain("protocol_read_chars(content_length)")
expect(src).to_contain("Content-Length: \" + str(_protocol_text_byte_len(body))")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/simple_mcp_malformed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Mcp Malformed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
