# T32 Cli Text Parser Specification

> <details>

<!-- sdn-diagram:id=t32_cli_text_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_text_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_text_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_text_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Text Parser Specification

## Scenarios

### T32 CLI Text Parsers

#### parse_break_list_output

#### parses breakpoint entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "enabled  address     symbol  type\n--------  ----------  ------  ------\nE:  0x08001234  main  Program\nE:  0x08002000  irq_handler  Program"
val rows = parse_break_list(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["enabled"]).to_equal("E:")
expect(rows[0]["address"]).to_equal("0x08001234")
expect(rows[0]["symbol"]).to_equal("main")
expect(rows[0]["type"]).to_equal("Program")
```

</details>

#### handles breakpoint with condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "E:  0x08001234  main  Program  i>10"
val rows = parse_break_list(raw)
expect(rows.len()).to_equal(1)
expect(rows[0]["condition"]).to_equal("i>10")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = parse_break_list("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_register_output

#### parses name=value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "R0=0x00000000  R1=0x12345678  R2=0xFF"
val rows = parse_register_out(raw)
expect(rows.len()).to_equal(3)
expect(rows[0]["name"]).to_equal("R0")
expect(rows[0]["value"]).to_equal("0x00000000")
expect(rows[1]["name"]).to_equal("R1")
expect(rows[1]["value"]).to_equal("0x12345678")
```

</details>

#### handles multiline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "R0=0x00  R1=0x01\nR2=0x02"
val rows = parse_register_out(raw)
expect(rows.len()).to_equal(3)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = parse_register_out("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_var_watch_output

#### parses name type value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "counter  int  42\nptr  char*  hello world"
val rows = parse_var_watch(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["name"]).to_equal("counter")
expect(rows[0]["type"]).to_equal("int")
expect(rows[0]["value"]).to_equal("42")
expect(rows[1]["value"]).to_equal("hello world")
```

</details>

#### skips header and separator lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "name  type  value\n---  ---  ---\ncounter  int  42"
val rows = parse_var_watch(raw)
expect(rows.len()).to_equal(1)
expect(rows[0]["name"]).to_equal("counter")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = parse_var_watch("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_trace_list_output

#### parses cycle address data type

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "cycle  address     data  type\n-----  ----------  ----  ----\n1000  0x08001234  0xAB  read\n1001  0x08001238  0xCD  write"
val rows = parse_trace_list(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["cycle"]).to_equal("1000")
expect(rows[0]["address"]).to_equal("0x08001234")
expect(rows[0]["data"]).to_equal("0xAB")
expect(rows[0]["type"]).to_equal("read")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = parse_trace_list("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_task_list_output

#### parses id name state priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "id  name  state  priority\n--  ----  -----  --------\n1  main_task  RUNNING  10\n2  idle  READY  0\n3  uart_rx  BLOCKED  5"
val rows = parse_task_list(raw)
expect(rows.len()).to_equal(3)
expect(rows[0]["id"]).to_equal("1")
expect(rows[0]["name"]).to_equal("main_task")
expect(rows[0]["state"]).to_equal("RUNNING")
expect(rows[0]["priority"]).to_equal("10")
expect(rows[2]["name"]).to_equal("uart_rx")
expect(rows[2]["state"]).to_equal("BLOCKED")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = parse_task_list("")
expect(rows.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_text_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CLI Text Parsers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
