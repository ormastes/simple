# Wine X86 64 Decode Specification

> <details>

<!-- sdn-diagram:id=wine_x86_64_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_x86_64_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_x86_64_decode_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_x86_64_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine X86 64 Decode Specification

## Scenarios

### Wine x86_64 hello decoder gate

#### rejects missing entrypoint instruction sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_x86_64_hello_decode_gate(_minimal_image())).to_equal("unsupported-entry-instruction:unsupported-opcode")
```

</details>

#### classifies supported and unsupported tiny instruction forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_hello_code(_minimal_image(), 0x210)
expect(wine_x86_64_instruction_at(data, 0x210)).to_equal("xor-rcx-rcx")
expect(wine_x86_64_instruction_len_at(data, 0x210)).to_equal(3)
expect(wine_x86_64_instruction_at(data, 0x213)).to_equal("call-rip-indirect")
expect(wine_x86_64_instruction_len_at(data, 0x213)).to_equal(6)
expect(wine_x86_64_instruction_at(data, 0x219)).to_equal("lea-rdx-rip-rel32")
expect(wine_x86_64_instruction_len_at(data, 0x219)).to_equal(7)
expect(wine_x86_64_instruction_at(data, 0x226)).to_equal("xor-ecx-ecx")
expect(wine_x86_64_instruction_len_at(data, 0x226)).to_equal(2)
expect(wine_x86_64_instruction_at(data, 0x22e)).to_equal("unsupported-opcode")
expect(wine_x86_64_instruction_len_at(data, 0x22e)).to_equal(0)
```

</details>

#### classifies common safe prologue and epilogue forms

1. var data =  zero bytes
   - Expected: wine_x86_64_instruction_at(data, 0) equals `push-rbp`
   - Expected: wine_x86_64_instruction_len_at(data, 0) equals `1`
   - Expected: wine_x86_64_instruction_at(data, 1) equals `mov-rbp-rsp`
   - Expected: wine_x86_64_instruction_len_at(data, 1) equals `3`
   - Expected: wine_x86_64_instruction_at(data, 4) equals `sub-rsp-imm8`
   - Expected: wine_x86_64_instruction_len_at(data, 4) equals `4`
   - Expected: wine_x86_64_instruction_at(data, 8) equals `nop`
   - Expected: wine_x86_64_instruction_len_at(data, 8) equals `1`
   - Expected: wine_x86_64_instruction_at(data, 9) equals `add-rsp-imm8`
   - Expected: wine_x86_64_instruction_len_at(data, 9) equals `4`
   - Expected: wine_x86_64_instruction_at(data, 13) equals `pop-rbp`
   - Expected: wine_x86_64_instruction_len_at(data, 13) equals `1`
   - Expected: wine_x86_64_instruction_at(data, 14) equals `ret`
   - Expected: wine_x86_64_instruction_len_at(data, 14) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(16)
data[0] = 0x55
data[1] = 0x48
data[2] = 0x89
data[3] = 0xe5
data[4] = 0x48
data[5] = 0x83
data[6] = 0xec
data[7] = 0x28
data[8] = 0x90
data[9] = 0x48
data[10] = 0x83
data[11] = 0xc4
data[12] = 0x28
data[13] = 0x5d
data[14] = 0xc3
expect(wine_x86_64_instruction_at(data, 0)).to_equal("push-rbp")
expect(wine_x86_64_instruction_len_at(data, 0)).to_equal(1)
expect(wine_x86_64_instruction_at(data, 1)).to_equal("mov-rbp-rsp")
expect(wine_x86_64_instruction_len_at(data, 1)).to_equal(3)
expect(wine_x86_64_instruction_at(data, 4)).to_equal("sub-rsp-imm8")
expect(wine_x86_64_instruction_len_at(data, 4)).to_equal(4)
expect(wine_x86_64_instruction_at(data, 8)).to_equal("nop")
expect(wine_x86_64_instruction_len_at(data, 8)).to_equal(1)
expect(wine_x86_64_instruction_at(data, 9)).to_equal("add-rsp-imm8")
expect(wine_x86_64_instruction_len_at(data, 9)).to_equal(4)
expect(wine_x86_64_instruction_at(data, 13)).to_equal("pop-rbp")
expect(wine_x86_64_instruction_len_at(data, 13)).to_equal(1)
expect(wine_x86_64_instruction_at(data, 14)).to_equal("ret")
expect(wine_x86_64_instruction_len_at(data, 14)).to_equal(1)
```

</details>

#### classifies truncated near-call bytes

1. var data =  zero bytes
   - Expected: wine_x86_64_instruction_at(data, 0) equals `truncated-call-rel32`
   - Expected: wine_x86_64_instruction_len_at(data, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(4)
data[0] = 0xe8
expect(wine_x86_64_instruction_at(data, 0)).to_equal("truncated-call-rel32")
expect(wine_x86_64_instruction_len_at(data, 0)).to_equal(0)
```

</details>

#### classifies truncated and unsupported rex imm8 arithmetic forms

1. var truncated =  zero bytes
   - Expected: wine_x86_64_instruction_at(truncated, 0) equals `truncated-rex-alu-imm8`
2. var unsupported =  zero bytes
   - Expected: wine_x86_64_instruction_at(unsupported, 0) equals `unsupported-rex-alu-imm8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var truncated = _zero_bytes(3)
truncated[0] = 0x48
truncated[1] = 0x83
truncated[2] = 0xec
expect(wine_x86_64_instruction_at(truncated, 0)).to_equal("truncated-rex-alu-imm8")
var unsupported = _zero_bytes(4)
unsupported[0] = 0x48
unsupported[1] = 0x83
unsupported[2] = 0xc0
unsupported[3] = 0x01
expect(wine_x86_64_instruction_at(unsupported, 0)).to_equal("unsupported-rex-alu-imm8")
```

</details>

#### classifies common rex imm32 stack allocation forms

1. var data =  zero bytes
2. data =  put u32 le
3. data =  put u32 le
   - Expected: wine_x86_64_instruction_at(data, 0) equals `sub-rsp-imm32`
   - Expected: wine_x86_64_instruction_len_at(data, 0) equals `7`
   - Expected: wine_x86_64_instruction_at(data, 7) equals `add-rsp-imm32`
   - Expected: wine_x86_64_instruction_len_at(data, 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(16)
data[0] = 0x48
data[1] = 0x81
data[2] = 0xec
data = _put_u32_le(data, 3, 0x120)
data[7] = 0x48
data[8] = 0x81
data[9] = 0xc4
data = _put_u32_le(data, 10, 0x120)
expect(wine_x86_64_instruction_at(data, 0)).to_equal("sub-rsp-imm32")
expect(wine_x86_64_instruction_len_at(data, 0)).to_equal(7)
expect(wine_x86_64_instruction_at(data, 7)).to_equal("add-rsp-imm32")
expect(wine_x86_64_instruction_len_at(data, 7)).to_equal(7)
```

</details>

#### rejects truncated and unsupported rex imm32 arithmetic forms

1. var truncated =  zero bytes
   - Expected: wine_x86_64_instruction_at(truncated, 0) equals `truncated-rex-alu-imm32`
2. var unsupported =  zero bytes
3. unsupported =  put u32 le
   - Expected: wine_x86_64_instruction_at(unsupported, 0) equals `unsupported-rex-alu-imm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var truncated = _zero_bytes(6)
truncated[0] = 0x48
truncated[1] = 0x81
truncated[2] = 0xec
expect(wine_x86_64_instruction_at(truncated, 0)).to_equal("truncated-rex-alu-imm32")
var unsupported = _zero_bytes(7)
unsupported[0] = 0x48
unsupported[1] = 0x81
unsupported[2] = 0xc0
unsupported = _put_u32_le(unsupported, 3, 0x120)
expect(wine_x86_64_instruction_at(unsupported, 0)).to_equal("unsupported-rex-alu-imm32")
```

</details>

#### classifies unsupported rex mov forms

1. var data =  zero bytes
   - Expected: wine_x86_64_instruction_at(data, 0) equals `unsupported-rex-mov`
   - Expected: wine_x86_64_instruction_len_at(data, 0) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(3)
data[0] = 0x48
data[1] = 0x89
data[2] = 0xc8
expect(wine_x86_64_instruction_at(data, 0)).to_equal("unsupported-rex-mov")
expect(wine_x86_64_instruction_len_at(data, 0)).to_equal(3)
```

</details>

#### scans a bounded safe prologue and epilogue window

1. var data =  zero bytes
   - Expected: scan.ok is true
   - Expected: scan.state equals `ready`
   - Expected: scan.end_offset equals `10`
   - Expected: scan.instruction_count equals `4`
   - Expected: scan.last_offset equals `9`
   - Expected: scan.last_instruction equals `ret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(16)
data[0] = 0x48
data[1] = 0x83
data[2] = 0xec
data[3] = 0x28
data[4] = 0x90
data[5] = 0x48
data[6] = 0x83
data[7] = 0xc4
data[8] = 0x28
data[9] = 0xc3
val scan = wine_x86_64_scan_window(data, 0, 10, 8)
expect(scan.ok).to_equal(true)
expect(scan.state).to_equal("ready")
expect(scan.end_offset).to_equal(10)
expect(scan.instruction_count).to_equal(4)
expect(scan.last_offset).to_equal(9)
expect(scan.last_instruction).to_equal("ret")
```

</details>

#### rejects unsupported opcodes while scanning

1. var data =  zero bytes
   - Expected: scan.ok is false
   - Expected: scan.state equals `unsupported-ff-instruction`
   - Expected: scan.last_offset equals `0`
   - Expected: scan.last_instruction equals `unsupported-ff-instruction`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(4)
data[0] = 0xff
val scan = wine_x86_64_scan_window(data, 0, 4, 8)
expect(scan.ok).to_equal(false)
expect(scan.state).to_equal("unsupported-ff-instruction")
expect(scan.last_offset).to_equal(0)
expect(scan.last_instruction).to_equal("unsupported-ff-instruction")
```

</details>

#### rejects truncated near calls while scanning

1. var data =  zero bytes
   - Expected: scan.ok is false
   - Expected: scan.state equals `truncated-call-rel32`
   - Expected: scan.last_offset equals `0`
   - Expected: scan.last_instruction equals `truncated-call-rel32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(4)
data[0] = 0xe8
val scan = wine_x86_64_scan_window(data, 0, 4, 8)
expect(scan.ok).to_equal(false)
expect(scan.state).to_equal("truncated-call-rel32")
expect(scan.last_offset).to_equal(0)
expect(scan.last_instruction).to_equal("truncated-call-rel32")
```

</details>

#### rejects instructions that cross the scan byte window

1. var data =  zero bytes
   - Expected: scan.ok is false
   - Expected: scan.state equals `instruction-window-overrun:sub-rsp-imm8`
   - Expected: scan.last_offset equals `0`
   - Expected: scan.last_instruction equals `sub-rsp-imm8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(8)
data[0] = 0x48
data[1] = 0x83
data[2] = 0xec
data[3] = 0x28
val scan = wine_x86_64_scan_window(data, 0, 3, 8)
expect(scan.ok).to_equal(false)
expect(scan.state).to_equal("instruction-window-overrun:sub-rsp-imm8")
expect(scan.last_offset).to_equal(0)
expect(scan.last_instruction).to_equal("sub-rsp-imm8")
```

</details>

#### rejects scan windows that exceed the instruction limit

1. var data =  zero bytes
   - Expected: scan.ok is false
   - Expected: scan.state equals `instruction-limit`
   - Expected: scan.instruction_count equals `2`
   - Expected: scan.last_offset equals `1`
   - Expected: scan.last_instruction equals `nop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _zero_bytes(8)
data[0] = 0x90
data[1] = 0x90
data[2] = 0xc3
val scan = wine_x86_64_scan_window(data, 0, 3, 2)
expect(scan.ok).to_equal(false)
expect(scan.state).to_equal("instruction-limit")
expect(scan.instruction_count).to_equal(2)
expect(scan.last_offset).to_equal(1)
expect(scan.last_instruction).to_equal("nop")
```

</details>

#### reports relative call targets for the import layer to validate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_x86_64_hello_decode_plan(_put_hello_code_with_bad_write_target(_minimal_image(), 0x210))
expect(plan.ok).to_equal(true)
expect(plan.get_std_handle_rva).to_equal(0x2060)
expect(plan.stdout_payload_rva).to_equal(0x2120)
expect(plan.write_file_rva).to_equal(0x2026)
expect(plan.exit_process_rva).to_equal(0x2070)
```

</details>

#### recognizes the hello call skeleton after a bounded frame-pointer prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_x86_64_hello_decode_plan(_put_hello_code_with_frame_prologue(_minimal_image(), 0x210))
expect(plan.ok).to_equal(true)
expect(plan.entry_rva).to_equal(0x2010)
expect(plan.sequence_rva).to_equal(0x2018)
expect(plan.sequence_end_rva).to_equal(0x2036)
```

</details>

#### recognizes the hello call skeleton after a bounded imm32 stack prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_x86_64_hello_decode_plan(_put_hello_code_with_wide_stack_prologue(_minimal_image(), 0x210))
expect(plan.ok).to_equal(true)
expect(plan.entry_rva).to_equal(0x2010)
expect(plan.sequence_rva).to_equal(0x201b)
expect(plan.sequence_end_rva).to_equal(0x2039)
```

</details>

#### recognizes the known hello call skeleton at the PE entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_x86_64_hello_decode_gate(_put_hello_code(_minimal_image(), 0x210))).to_equal("ready")
```

</details>

#### recognizes the hello call skeleton after a bounded safe entry prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_x86_64_hello_decode_plan(_put_hello_code_with_safe_prologue(_minimal_image(), 0x210))
expect(plan.ok).to_equal(true)
expect(plan.entry_rva).to_equal(0x2010)
expect(plan.sequence_rva).to_equal(0x2015)
expect(plan.sequence_end_rva).to_equal(0x2033)
expect(plan.get_std_handle_rva).to_equal(0x2060)
expect(plan.stdout_payload_rva).to_equal(0x2120)
expect(plan.write_file_rva).to_equal(0x2068)
expect(plan.exit_process_rva).to_equal(0x2070)
```

</details>

#### returns a structured hello execution plan from the decoded entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_x86_64_hello_decode_plan(_put_hello_code(_minimal_image(), 0x210))
expect(plan.ok).to_equal(true)
expect(plan.entry_rva).to_equal(0x2010)
expect(plan.sequence_rva).to_equal(0x2010)
expect(plan.sequence_end_rva).to_equal(0x202e)
expect(plan.instruction_sequence).to_equal("xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32 call-rip-indirect xor-ecx-ecx call-rip-indirect")
expect(plan.instruction_count).to_equal(6)
expect(plan.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(plan.call_count).to_equal(3)
expect(plan.get_std_handle_rva).to_equal(0x2060)
expect(plan.stdout_payload_rva).to_equal(0x2120)
expect(plan.write_file_rva).to_equal(0x2068)
expect(plan.exit_process_rva).to_equal(0x2070)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_x86_64_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine x86_64 hello decoder gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
