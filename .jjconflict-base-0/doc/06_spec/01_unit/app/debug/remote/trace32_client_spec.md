# Trace32 Client Specification

> <details>

<!-- sdn-diagram:id=trace32_client_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trace32_client_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trace32_client_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trace32_client_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trace32 Client Specification

## Scenarios

### Trace32Parser

#### parse_variables

#### parses variable list with name, type, value

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "counter  int  42\nptr  char*  0x20001000\nflag  bool  1"
val vars = tp_parse_variables(raw)
expect(vars.len()).to_equal(3)
expect(vars[0].name).to_equal("counter")
expect(vars[0].type_name).to_equal("int")
expect(vars[0].value).to_equal("42")
expect(vars[1].name).to_equal("ptr")
expect(vars[1].type_name).to_equal("char*")
expect(vars[2].name).to_equal("flag")
expect(vars[2].value).to_equal("1")
```

</details>

#### skips empty lines and header lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "name  type  value\n---  ---  ---\n\ncounter  int  42"
val vars = tp_parse_variables(raw)
expect(vars.len()).to_equal(1)
expect(vars[0].name).to_equal("counter")
```

</details>

#### handles two-column output (name and value only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "x  0xFF"
val vars = tp_parse_variables(raw)
expect(vars.len()).to_equal(1)
expect(vars[0].name).to_equal("x")
expect(vars[0].value).to_equal("0xFF")
expect(vars[0].type_name).to_equal("")
```

</details>

#### returns empty list for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vars = tp_parse_variables("")
expect(vars.len()).to_equal(0)
```

</details>

#### parse_stack_trace

#### parses stack frames with function and location

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "#0  0x08001234  main  main.c:42\n#1  0x08001000  reset_handler  startup.s:10"
val frames = tp_parse_stack_trace(raw)
expect(frames.len()).to_equal(2)
expect(frames[0].index).to_equal(0)
expect(frames[0].function_name).to_equal("main")
expect(frames[0].file).to_equal("main.c")
expect(frames[0].line).to_equal(42)
expect(frames[1].index).to_equal(1)
expect(frames[1].function_name).to_equal("reset_handler")
```

</details>

#### skips empty and separator lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "---\n\n#0  0x08001234  main  main.c:42"
val frames = tp_parse_stack_trace(raw)
expect(frames.len()).to_equal(1)
```

</details>

#### returns empty list for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frames = tp_parse_stack_trace("")
expect(frames.len()).to_equal(0)
```

</details>

#### parse_memory_dump

#### parses hex byte dump with address prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "0x20000000: 01 02 03 04\n0x20000004: 0A 0B 0C 0D"
val bytes = tp_parse_memory_dump(raw)
expect(bytes.len()).to_equal(8)
expect(bytes[0]).to_equal(1)
expect(bytes[1]).to_equal(2)
expect(bytes[4]).to_equal(10)
expect(bytes[7]).to_equal(13)
```

</details>

#### parses dump without address prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "FF 00 AB CD"
val bytes = tp_parse_memory_dump(raw)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(255)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(171)
expect(bytes[3]).to_equal(205)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = tp_parse_memory_dump("")
expect(bytes.len()).to_equal(0)
```

</details>

#### parse_register_value

#### parses hex register value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tp_parse_register_value("0x12345678")
match result:
    Ok(v): expect(v).to_equal(305419896)
    Err(_): expect(true).to_equal(false)
```

</details>

#### parses uppercase hex value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tp_parse_register_value("0XABCDEF00")
match result:
    Ok(v): expect(v).to_equal(2882400000)
    Err(_): expect(true).to_equal(false)
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tp_parse_register_value("0x0")
match result:
    Ok(v): expect(v).to_equal(0)
    Err(_): expect(true).to_equal(false)
```

</details>

#### parses decimal value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tp_parse_register_value("12345")
match result:
    Ok(v): expect(v).to_equal(12345)
    Err(_): expect(true).to_equal(false)
```

</details>

#### trims whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tp_parse_register_value("  0xFF  ")
match result:
    Ok(v): expect(v).to_equal(255)
    Err(_): expect(true).to_equal(false)
```

</details>

#### returns error for invalid input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tp_parse_register_value("not_a_number")
match result:
    Ok(_): expect(true).to_equal(false)
    Err(e): expect(e).to_contain("cannot parse")
```

</details>

#### parse_register_list

#### parses register=value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "R0=0x00000000  R1=0x12345678  R2=0xFF"
val regs = tp_parse_register_list(raw)
expect(regs["R0"]).to_equal(0)
expect(regs["R1"]).to_equal(305419896)
expect(regs["R2"]).to_equal(255)
```

</details>

#### handles multiline register output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "R0=0x00  R1=0x01\nR2=0x02  R3=0x03"
val regs = tp_parse_register_list(raw)
expect(regs["R0"]).to_equal(0)
expect(regs["R1"]).to_equal(1)
expect(regs["R2"]).to_equal(2)
expect(regs["R3"]).to_equal(3)
```

</details>

#### returns empty dict for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regs = tp_parse_register_list("")
expect(regs.keys().len()).to_equal(0)
```

</details>

#### normalize_current_status

#### maps STATE.RUN true to running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_normalize_current_status("1", "RUN", "Attach")).to_equal("running")
```

</details>

#### maps break state to stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_normalize_current_status("0", "Break", "Attach")).to_equal("stopped")
```

</details>

#### maps down state to disconnected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_normalize_current_status("0", "Down", "Down")).to_equal("disconnected")
```

</details>

#### hex utilities

#### converts integer to hex string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_to_hex(0)).to_equal("0x0")
expect(tp_to_hex(255)).to_equal("0xff")
expect(tp_to_hex(4096)).to_equal("0x1000")
```

</details>

#### converts byte to two-char hex string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_byte_to_hex(0)).to_equal("00")
expect(tp_byte_to_hex(255)).to_equal("ff")
expect(tp_byte_to_hex(171)).to_equal("ab")
```

</details>

#### parses hex byte string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_parse_hex_byte("FF")).to_equal(255)
expect(tp_parse_hex_byte("00")).to_equal(0)
expect(tp_parse_hex_byte("AB")).to_equal(171)
```

</details>

#### returns -1 for invalid hex byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tp_parse_hex_byte("GG")).to_equal(-1)
expect(tp_parse_hex_byte("X")).to_equal(-1)
```

</details>

#### split_whitespace

#### splits on spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = tp_split_whitespace("hello world")
expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("hello")
expect(parts[1]).to_equal("world")
```

</details>

#### handles multiple spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = tp_split_whitespace("a   b   c")
expect(parts.len()).to_equal(3)
```

</details>

#### handles tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = tp_split_whitespace("a\tb\tc")
expect(parts.len()).to_equal(3)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = tp_split_whitespace("")
expect(parts.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/trace32_client_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Trace32Parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
