# T32 Cli Render Specification

> <details>

<!-- sdn-diagram:id=t32_cli_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_render_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Render Specification

## Scenarios

### T32 CLI Render

#### scalar results

#### renders scalar value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_scalar("42")
val output = render_result(result)
expect(output).to_equal("42")
```

</details>

#### renders scalar with title

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_scalar_titled("Register PC", "0x08001000")
val output = render_result(result)
expect(output).to_equal("Register PC: 0x08001000")
```

</details>

#### table results

#### renders table with header and separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows: [[text]] = [["Name", "Value"], ["PC", "0x1000"], ["SP", "0x2000"]]
val result = make_table("Registers", rows)
val output = render_result(result)
expect(output).to_contain("Registers:")
expect(output).to_contain("Name")
expect(output).to_contain("Value")
expect(output).to_contain("PC")
expect(output).to_contain("SP")
# Header separator line of dashes should be present
expect(output).to_contain("----")
```

</details>

#### renders empty table as (empty)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_table("Empty", [])
val output = render_result(result)
expect(output).to_equal("Empty: (empty)")
```

</details>

#### kv results

#### renders aligned key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs: [[text]] = [["host", "localhost"], ["port", "20000"]]
val result = make_kv("Session", pairs)
val output = render_result(result)
expect(output).to_start_with("Session:")
expect(output).to_contain("host")
expect(output).to_contain("localhost")
expect(output).to_contain("port")
expect(output).to_contain("20000")
```

</details>

#### list results

#### renders bulleted items

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [text] = ["alpha", "beta", "gamma"]
val result = make_list("Items", items)
val output = render_result(result)
expect(output).to_start_with("Items:")
expect(output).to_contain("  - alpha")
expect(output).to_contain("  - beta")
expect(output).to_contain("  - gamma")
```

</details>

#### raw output

#### passes through raw text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_raw("some raw output\nline two")
val output = render_result(result)
expect(output).to_equal("some raw output\nline two")
```

</details>

#### error formatting

#### formats error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_error("Connection lost")
expect(output).to_equal("Error: Connection lost")
```

</details>

#### formats empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_error("")
expect(output).to_equal("Error: ")
```

</details>

#### gui_status footer

#### appends gui status footer to scalar

1. var result = make scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = make_scalar("ok")
result.gui_status = "{\"cpu_state\":\"stopped\",\"practice_state\":\"idle\"}"
val output = render_result(result)
expect(output).to_contain("ok")
expect(output).to_contain("[CPU: stopped | PRACTICE: idle]")
```

</details>

#### skips empty gui status

1. var result = make scalar
   - Expected: output equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = make_scalar("ok")
result.gui_status = ""
val output = render_result(result)
expect(output).to_equal("ok")
```

</details>

#### skips empty object gui status

1. var result = make scalar
   - Expected: output equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = make_scalar("ok")
result.gui_status = "{}"
val output = render_result(result)
expect(output).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CLI Render

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
