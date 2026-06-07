# Window Capture Specification

> <details>

<!-- sdn-diagram:id=window_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_capture_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Capture Specification

## Scenarios

### T32 Window Text Parsing

#### parses break list output

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "E: 0x08001234  main          Program  Exec\nE: 0x08005678  task_handler  Program  Exec"
val lines = raw.split("\n")
expect(lines.len()).to_equal(2)
val parts = split_ws(lines[0])
expect(parts.len()).to_be_greater_than(2)
expect(parts[0]).to_equal("E:")
expect(parts[1]).to_equal("0x08001234")
expect(parts[2]).to_equal("main")
```

</details>

#### parses register view output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "R0=0x00000000  R1=0x20001000  R2=0xDEADBEEF  R3=0x00000001"
val tokens = split_ws(raw)
expect(tokens.len()).to_equal(4)
val pair = tokens[0].split("=")
expect(pair[0]).to_equal("R0")
expect(pair[1]).to_equal("0x00000000")
```

</details>

#### parses var watch output

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "count    int    42\nname     char*  \"hello\"\nflag     bool   true"
val lines = raw.split("\n")
expect(lines.len()).to_equal(3)
val parts = split_ws(lines[0])
expect(parts[0]).to_equal("count")
expect(parts[1]).to_equal("int")
expect(parts[2]).to_equal("42")
```

</details>

#### handles empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = ""
val lines = raw.split("\n")
# empty string split gives 1 empty element
expect(lines[0]).to_equal("")
```

</details>

#### parses tabular with header

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "Name     Type     Value\n---      ----     -----\ncount    int      42\nflag     bool     true"
val lines = raw.split("\n")
expect(lines.len()).to_equal(4)
# Skip header and separator
val data_line = lines[2]
val parts = split_ws(data_line)
expect(parts[0]).to_equal("count")
```

</details>

#### parses multi-line register dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "R0=0x00  R1=0x01  R2=0x02\nR3=0x03  R4=0x04  R5=0x05"
val lines = raw.split("\n")
expect(lines.len()).to_equal(2)
val line1_tokens = split_ws(lines[0])
expect(line1_tokens.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/trace32/window_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Window Text Parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
