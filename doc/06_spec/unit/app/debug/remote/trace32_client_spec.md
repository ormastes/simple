# trace32_client_spec

> Purpose: Prove that Trace32Parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# trace32_client_spec

Purpose: Prove that Trace32Parser.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/trace32_client_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Trace32Parser.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Trace32Parser

#### parse_variables

#### parses variable list with name, type, value

- parses variable list with name, type, value
- Verify: parses variable list with name, type, value
   - Expected: vars.len() equals `3`
   - Expected: vars[0].name equals `counter`
   - Expected: vars[0].type_name equals `int`
   - Expected: vars[0].value equals `42`
   - Expected: vars[1].name equals `ptr`
   - Expected: vars[1].type_name equals `char*`
   - Expected: vars[2].name equals `flag`
   - Expected: vars[2].value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses variable list with name, type, value")
step("Verify: parses variable list with name, type, value")
# @req: REQ-APP-DEBUG-001
val raw = "counter  int  42\nptr  char*  0x20001000\nflag  bool  1"
val vars = tp_parse_variables(raw)
expect(vars.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
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

- skips empty lines and header lines
- Verify: skips empty lines and header lines
   - Expected: vars.len() equals `1`
   - Expected: vars[0].name equals `counter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips empty lines and header lines")
step("Verify: skips empty lines and header lines")
val raw = "name  type  value\n---  ---  ---\n\ncounter  int  42"
val vars = tp_parse_variables(raw)
expect(vars.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vars[0].name).to_equal("counter")
```

</details>

#### handles two-column output (name and value only)

- handles two-column output (name and value only)
- Verify: handles two-column output (name and value only)
   - Expected: vars.len() equals `1`
   - Expected: vars[0].name equals `x`
   - Expected: vars[0].value equals `0xFF`
   - Expected: vars[0].type_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles two-column output (name and value only)")
step("Verify: handles two-column output (name and value only)")
val raw = "x  0xFF"
val vars = tp_parse_variables(raw)
expect(vars.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vars[0].name).to_equal("x")
expect(vars[0].value).to_equal("0xFF")
expect(vars[0].type_name).to_equal("")
```

</details>

#### returns empty list for empty input

- returns empty list for empty input
- Verify: returns empty list for empty input
   - Expected: vars.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list for empty input")
step("Verify: returns empty list for empty input")
val vars = tp_parse_variables("")
expect(vars.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### parse_stack_trace

#### parses stack frames with function and location

- parses stack frames with function and location
- Verify: parses stack frames with function and location
   - Expected: frames.len() equals `2`
   - Expected: frames[0].index equals `0`
   - Expected: frames[0].function_name equals `main`
   - Expected: frames[0].file equals `main.c`
   - Expected: frames[0].line equals `42`
   - Expected: frames[1].index equals `1`
   - Expected: frames[1].function_name equals `reset_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses stack frames with function and location")
step("Verify: parses stack frames with function and location")
val raw = "#0  0x08001234  main  main.c:42\n#1  0x08001000  reset_handler  startup.s:10"
val frames = tp_parse_stack_trace(raw)
expect(frames.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(frames[0].index).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(frames[0].function_name).to_equal("main")
expect(frames[0].file).to_equal("main.c")
expect(frames[0].line).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(frames[1].index).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(frames[1].function_name).to_equal("reset_handler")
```

</details>

#### skips empty and separator lines

- skips empty and separator lines
- Verify: skips empty and separator lines
   - Expected: frames.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips empty and separator lines")
step("Verify: skips empty and separator lines")
val raw = "---\n\n#0  0x08001234  main  main.c:42"
val frames = tp_parse_stack_trace(raw)
expect(frames.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns empty list for empty input

- returns empty list for empty input
- Verify: returns empty list for empty input
   - Expected: frames.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list for empty input")
step("Verify: returns empty list for empty input")
val frames = tp_parse_stack_trace("")
expect(frames.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### parse_memory_dump

#### parses hex byte dump with address prefix

- parses hex byte dump with address prefix
- Verify: parses hex byte dump with address prefix
   - Expected: bytes.len() equals `8`
   - Expected: bytes[0] equals `1`
   - Expected: bytes[1] equals `2`
   - Expected: bytes[4] equals `10`
   - Expected: bytes[7] equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex byte dump with address prefix")
step("Verify: parses hex byte dump with address prefix")
val raw = "0x20000000: 01 02 03 04\n0x20000004: 0A 0B 0C 0D"
val bytes = tp_parse_memory_dump(raw)
expect(bytes.len()).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(bytes[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(bytes[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(bytes[4]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(bytes[7]).to_equal(13)  # oracle: 13 — named expected value from the requirement
```

</details>

#### parses dump without address prefix

- parses dump without address prefix
- Verify: parses dump without address prefix
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `255`
   - Expected: bytes[1] equals `0`
   - Expected: bytes[2] equals `171`
   - Expected: bytes[3] equals `205`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses dump without address prefix")
step("Verify: parses dump without address prefix")
val raw = "FF 00 AB CD"
val bytes = tp_parse_memory_dump(raw)
expect(bytes.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(bytes[0]).to_equal(255)  # oracle: 255 — named expected value from the requirement
expect(bytes[1]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(bytes[2]).to_equal(171)  # oracle: 171 — named expected value from the requirement
expect(bytes[3]).to_equal(205)  # oracle: 205 — named expected value from the requirement
```

</details>

#### returns empty for empty input

- returns empty for empty input
- Verify: returns empty for empty input
   - Expected: bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
step("Verify: returns empty for empty input")
val bytes = tp_parse_memory_dump("")
expect(bytes.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### parse_register_value

#### parses hex register value

- parses hex register value
- Verify: parses hex register value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex register value")
step("Verify: parses hex register value")
val result = tp_parse_register_value("0x12345678")
match result:
    Ok(v): expect(v).to_equal(305419896)  # oracle: 305419896 — named expected value from the requirement
    Err(_): expect(true).to_equal(false)
```

</details>

#### parses uppercase hex value

- parses uppercase hex value
- Verify: parses uppercase hex value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses uppercase hex value")
step("Verify: parses uppercase hex value")
val result = tp_parse_register_value("0XABCDEF00")
match result:
    Ok(v): expect(v).to_equal(2882400000)  # oracle: 2882400000 — named expected value from the requirement
    Err(_): expect(true).to_equal(false)
```

</details>

#### parses zero

- parses zero
- Verify: parses zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
step("Verify: parses zero")
val result = tp_parse_register_value("0x0")
match result:
    Ok(v): expect(v).to_equal(0)  # oracle: 0 — named expected value from the requirement
    Err(_): expect(true).to_equal(false)
```

</details>

#### parses decimal value

- parses decimal value
- Verify: parses decimal value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses decimal value")
step("Verify: parses decimal value")
val result = tp_parse_register_value("12345")
match result:
    Ok(v): expect(v).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
    Err(_): expect(true).to_equal(false)
```

</details>

#### trims whitespace

- trims whitespace
- Verify: trims whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace")
step("Verify: trims whitespace")
val result = tp_parse_register_value("  0xFF  ")
match result:
    Ok(v): expect(v).to_equal(255)  # oracle: 255 — named expected value from the requirement
    Err(_): expect(true).to_equal(false)
```

</details>

#### returns error for invalid input

- returns error for invalid input
- Verify: returns error for invalid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for invalid input")
step("Verify: returns error for invalid input")
val result = tp_parse_register_value("not_a_number")
match result:
    Ok(_): expect(true).to_equal(false)
    Err(e): expect(e).to_contain("cannot parse")
```

</details>

#### parse_register_list

#### parses register=value pairs

- parses register=value pairs
- Verify: parses register=value pairs
   - Expected: regs["R0"] equals `0`
   - Expected: regs["R1"] equals `305419896`
   - Expected: regs["R2"] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses register=value pairs")
step("Verify: parses register=value pairs")
val raw = "R0=0x00000000  R1=0x12345678  R2=0xFF"
val regs = tp_parse_register_list(raw)
expect(regs["R0"]).to_equal(0)
expect(regs["R1"]).to_equal(305419896)
expect(regs["R2"]).to_equal(255)
```

</details>

#### handles multiline register output

- handles multiline register output
- Verify: handles multiline register output
   - Expected: regs["R0"] equals `0`
   - Expected: regs["R1"] equals `1`
   - Expected: regs["R2"] equals `2`
   - Expected: regs["R3"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline register output")
step("Verify: handles multiline register output")
val raw = "R0=0x00  R1=0x01\nR2=0x02  R3=0x03"
val regs = tp_parse_register_list(raw)
expect(regs["R0"]).to_equal(0)
expect(regs["R1"]).to_equal(1)
expect(regs["R2"]).to_equal(2)
expect(regs["R3"]).to_equal(3)
```

</details>

#### returns empty dict for empty input

- returns empty dict for empty input
- Verify: returns empty dict for empty input
   - Expected: regs.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty dict for empty input")
step("Verify: returns empty dict for empty input")
val regs = tp_parse_register_list("")
expect(regs.keys().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### normalize_current_status

#### maps STATE.RUN true to running

- maps STATE.RUN true to running
- Verify: maps STATE.RUN true to running
   - Expected: tp_normalize_current_status("1", "RUN", "Attach") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps STATE.RUN true to running")
step("Verify: maps STATE.RUN true to running")
expect(tp_normalize_current_status("1", "RUN", "Attach")).to_equal("running")
```

</details>

#### maps break state to stopped

- maps break state to stopped
- Verify: maps break state to stopped
   - Expected: tp_normalize_current_status("0", "Break", "Attach") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps break state to stopped")
step("Verify: maps break state to stopped")
expect(tp_normalize_current_status("0", "Break", "Attach")).to_equal("stopped")
```

</details>

#### maps down state to disconnected

- maps down state to disconnected
- Verify: maps down state to disconnected
   - Expected: tp_normalize_current_status("0", "Down", "Down") equals `disconnected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps down state to disconnected")
step("Verify: maps down state to disconnected")
expect(tp_normalize_current_status("0", "Down", "Down")).to_equal("disconnected")
```

</details>

#### hex utilities

#### converts integer to hex string

- converts integer to hex string
- Verify: converts integer to hex string
   - Expected: tp_to_hex(0) equals `0x0`
   - Expected: tp_to_hex(255) equals `0xff`
   - Expected: tp_to_hex(4096) equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts integer to hex string")
step("Verify: converts integer to hex string")
expect(tp_to_hex(0)).to_equal("0x0")
expect(tp_to_hex(255)).to_equal("0xff")
expect(tp_to_hex(4096)).to_equal("0x1000")
```

</details>

#### converts byte to two-char hex string

- converts byte to two-char hex string
- Verify: converts byte to two-char hex string
   - Expected: tp_byte_to_hex(0) equals `00`
   - Expected: tp_byte_to_hex(255) equals `ff`
   - Expected: tp_byte_to_hex(171) equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts byte to two-char hex string")
step("Verify: converts byte to two-char hex string")
expect(tp_byte_to_hex(0)).to_equal("00")
expect(tp_byte_to_hex(255)).to_equal("ff")
expect(tp_byte_to_hex(171)).to_equal("ab")
```

</details>

#### parses hex byte string

- parses hex byte string
- Verify: parses hex byte string
   - Expected: tp_parse_hex_byte("FF") equals `255`
   - Expected: tp_parse_hex_byte("00") equals `0`
   - Expected: tp_parse_hex_byte("AB") equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex byte string")
step("Verify: parses hex byte string")
expect(tp_parse_hex_byte("FF")).to_equal(255)
expect(tp_parse_hex_byte("00")).to_equal(0)
expect(tp_parse_hex_byte("AB")).to_equal(171)
```

</details>

#### returns -1 for invalid hex byte

- returns -1 for invalid hex byte
- Verify: returns -1 for invalid hex byte
   - Expected: tp_parse_hex_byte("GG") equals `-1`
   - Expected: tp_parse_hex_byte("X") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for invalid hex byte")
step("Verify: returns -1 for invalid hex byte")
expect(tp_parse_hex_byte("GG")).to_equal(-1)
expect(tp_parse_hex_byte("X")).to_equal(-1)
```

</details>

#### split_whitespace

#### splits on spaces

- splits on spaces
- Verify: splits on spaces
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals `hello`
   - Expected: parts[1] equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits on spaces")
step("Verify: splits on spaces")
val parts = tp_split_whitespace("hello world")
expect(parts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(parts[0]).to_equal("hello")
expect(parts[1]).to_equal("world")
```

</details>

#### handles multiple spaces

- handles multiple spaces
- Verify: handles multiple spaces
   - Expected: parts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple spaces")
step("Verify: handles multiple spaces")
val parts = tp_split_whitespace("a   b   c")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### handles tabs

- handles tabs
- Verify: handles tabs
   - Expected: parts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles tabs")
step("Verify: handles tabs")
val parts = tp_split_whitespace("a\tb\tc")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### returns empty for empty input

- returns empty for empty input
- Verify: returns empty for empty input
   - Expected: parts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
step("Verify: returns empty for empty input")
val parts = tp_split_whitespace("")
expect(parts.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-DEBUG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b6a9bd4e3e9a897cbea828168211af2fb772be8a056ce1baa4632bcd748fe69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b6a9bd4e3e9a897cbea828168211af2fb772be8a056ce1baa4632bcd748fe69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b6a9bd4e3e9a897cbea828168211af2fb772be8a056ce1baa4632bcd748fe69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/debug/remote/trace32_client_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/trace32_client_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/trace32_client_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/trace32_client_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/trace32_client_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/trace32_client_spec.spl:300:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses variable list with name, type, value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/trace32_client_spec.spl:316:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips empty lines and header lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/trace32_client_spec.spl:325:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles two-column output (name and value only)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
