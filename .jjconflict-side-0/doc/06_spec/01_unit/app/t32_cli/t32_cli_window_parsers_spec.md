# T32 Cli Window Parsers Specification

> <details>

<!-- sdn-diagram:id=t32_cli_window_parsers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_window_parsers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_window_parsers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_window_parsers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Window Parsers Specification

## Scenarios

### T32 CLI Window Parsers (all 16)

#### parse_stack_frame_output

#### parses stack frame entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "#0  0x08001234  main+0x10  src/main.c:42\n#1  0x08001000  SystemInit  src/system.c:15"
val rows = p_stack_frame(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["frame_id"]).to_equal("#0")
expect(rows[0]["address"]).to_equal("0x08001234")
expect(rows[0]["function"]).to_equal("main+0x10")
expect(rows[0]["file_line"]).to_equal("src/main.c:42")
```

</details>

#### handles frame without file info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "#0  0x08001234  _start"
val rows = p_stack_frame(raw)
expect(rows.len()).to_equal(1)
expect(rows[0]["file_line"]).to_equal("")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_stack_frame("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_memory_dump_output

#### parses memory dump lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "D:0x20000000: 48 65 6C 6C 6F 20 57 6F  Hello Wo\nD:0x20000008: 72 6C 64 00 00 00 00 00  rld....."
val rows = p_memory_dump(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["address"]).to_equal("D:0x20000000:")
expect(rows[0]["hex_bytes"]).to_contain("48")
expect(rows[0]["ascii"]).to_contain("Hello")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_memory_dump("")
expect(rows.len()).to_equal(0)
```

</details>

#### skips comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "# comment\nD:0x20000000: AA BB  xy"
val rows = p_memory_dump(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### parse_source_list_output

#### parses source listing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "42  0x08001234  printf(\"hello\");\n43  0x08001238  return 0;"
val rows = p_source_list(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["line_number"]).to_equal("42")
expect(rows[0]["address"]).to_equal("0x08001234")
expect(rows[0]["source"]).to_contain("printf")
```

</details>

#### skips header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "line  address  source\n42  0x08001234  code"
val rows = p_source_list(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_source_list("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_coverage_output

#### parses coverage entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "main           85.3%   1024\nirq_handler    42.1%   256"
val rows = p_coverage(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["function"]).to_equal("main")
expect(rows[0]["percent"]).to_equal("85.3%")
expect(rows[0]["hits"]).to_equal("1024")
```

</details>

#### skips header and separator lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "function  percent  hits\n--------  -------  ----\nmain  90%  100"
val rows = p_coverage(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_coverage("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_symbol_browse_output

#### parses symbol entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "main           0x08001000  0x00000100  Code\nirq_handler    0x08002000  0x00000080  Code"
val rows = p_symbol_browse(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["name"]).to_equal("main")
expect(rows[0]["address"]).to_equal("0x08001000")
expect(rows[0]["size"]).to_equal("0x00000100")
expect(rows[0]["type"]).to_equal("Code")
```

</details>

#### skips header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "name  address  size  type\nmain  0x1000  0x100  Code"
val rows = p_symbol_browse(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_symbol_browse("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_perf_output

#### parses performance entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "main  12.5ms  1024  42.1%\nidle  87.5ms  2048  57.9%"
val rows = p_perf(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["module"]).to_equal("main")
expect(rows[0]["time"]).to_equal("12.5ms")
expect(rows[0]["calls"]).to_equal("1024")
expect(rows[0]["percent"]).to_equal("42.1%")
```

</details>

#### skips header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "module  time  calls  percent\nmain  1ms  10  50%"
val rows = p_perf(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_perf("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_mmu_output

#### parses MMU entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "0x00000000  0x80000000  0x00100000  RWX\n0x10000000  0x90000000  0x00200000  RW-"
val rows = p_mmu(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["virt_addr"]).to_equal("0x00000000")
expect(rows[0]["phys_addr"]).to_equal("0x80000000")
expect(rows[0]["size"]).to_equal("0x00100000")
expect(rows[0]["perms"]).to_equal("RWX")
```

</details>

#### skips header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "virt_addr  phys_addr  size  perms\n0x0  0x1  0x2  RW"
val rows = p_mmu(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_mmu("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_peripheral_output

#### parses peripheral entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "GPIOA_MODER  0x48000000  0x28000000  [31:0]\nGPIOA_ODR  0x48000014  0x00000001  [15:0]"
val rows = p_peripheral(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["name"]).to_equal("GPIOA_MODER")
expect(rows[0]["address"]).to_equal("0x48000000")
expect(rows[0]["value"]).to_equal("0x28000000")
expect(rows[0]["bits"]).to_equal("[31:0]")
```

</details>

#### skips header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "name  address  value  bits\nREG  0x0  0x1  [7:0]"
val rows = p_peripheral(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_peripheral("")
expect(rows.len()).to_equal(0)
```

</details>

#### parse_data_list_output

#### parses disassembly entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "0x08001234  BL  main\n0x08001238  MOV R0, #0  _start"
val rows = p_data_list(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["address"]).to_equal("0x08001234")
expect(rows[0]["instruction"]).to_equal("BL")
expect(rows[0]["symbol"]).to_equal("main")
```

</details>

#### handles multi-word instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "0x08001238  MOV R0, #0  _start"
val rows = p_data_list(raw)
expect(rows.len()).to_equal(1)
expect(rows[0]["instruction"]).to_contain("MOV")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_data_list("")
expect(rows.len()).to_equal(0)
```

</details>

#### skips header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "address  instruction  symbol\n0x1000  NOP  main"
val rows = p_data_list(raw)
expect(rows.len()).to_equal(1)
```

</details>

#### parse_area_output

#### parses area lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "Hello World\nSecond line\nThird"
val lines = p_area(raw)
expect(lines.len()).to_equal(3)
expect(lines[0]).to_equal("Hello World")
expect(lines[1]).to_equal("Second line")
```

</details>

#### returns single line for single line input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = p_area("only one")
expect(lines.len()).to_equal(1)
expect(lines[0]).to_equal("only one")
```

</details>

#### parse_var_local_output (reuse var_watch)

#### parses local variable entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "counter  int  42\nptr  char*  hello world"
val rows = p_var_watch(raw)
expect(rows.len()).to_equal(2)
expect(rows[0]["name"]).to_equal("counter")
expect(rows[0]["type"]).to_equal("int")
expect(rows[0]["value"]).to_equal("42")
expect(rows[1]["value"]).to_equal("hello world")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = p_var_watch("")
expect(rows.len()).to_equal(0)
```

</details>

#### edge cases

#### handles extra whitespace in stack frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "  #0    0x08001234    main   "
val rows = p_stack_frame(raw)
expect(rows.len()).to_equal(1)
expect(rows[0]["function"]).to_equal("main")
```

</details>

#### handles missing columns gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "0x08001234"
val rows = p_data_list(raw)
expect(rows.len()).to_equal(0)
```

</details>

#### handles empty lines mixed with data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "\nmain  85%  100\n\nirq  42%  50\n"
val rows = p_coverage(raw)
expect(rows.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_window_parsers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CLI Window Parsers (all 16)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
