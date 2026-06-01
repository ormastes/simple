# Rtl Command Specification

## Scenarios

### RTL command parser

#### parses bench suite and target

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = parse_rtl_command(["rtl", "bench", "--suite=smoke", "--target=ice40"])
check(command.is_bench())
expect command.suite == "smoke"
expect command.target == "ice40"
```

</details>

#### parses compare baselines

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = parse_rtl_command(["rtl", "compare", "--baseline=old", "--candidate=new"])
check(command.is_compare())
expect command.baseline == "old"
expect command.candidate == "new"
```

</details>

#### parses qor report command

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = parse_rtl_command(["rtl", "qor", "report", "--design=rv32i_core"])
check(command.is_report())
expect command.design == "rv32i_core"
```

</details>

#### parses rtl explain command

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = parse_rtl_command(["rtl", "explain", "--map=core.vhd.map.json", "--vhdl-line=8"])
check(command.is_explain())
expect command.map_path == "core.vhd.map.json"
expect command.vhdl_line == 8
```

</details>

#### renders a bench preview report

1. check

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = parse_rtl_command(["rtl", "bench", "--suite=smoke", "--target=generic"])
val markdown = render_rtl_bench_preview(command)
check(markdown.contains("RTL QoR Run"))
check(markdown.contains("ghdl-yosys"))
```

</details>

#### renders an explain preview from source map JSON

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = parse_rtl_command(["rtl", "explain", "--vhdl-line=8"])
val map_json = "{\"ports\":[{\"name\":\"a\",\"originalName\":\"a\",\"sanitizedName\":\"a\",\"line\":8,\"hwirId\":\"port:a:8\",\"sourceLine\":2}]}"
val text = render_rtl_explain_preview(command, map_json)
check(text.contains("port:a:8"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/rtl/rtl_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RTL command parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

