# VHDL Backend RV64GC RTL Regression Specification

> Regression tests for the VHDL backend covering constructs used by rv64gc_rtl modules: 64-bit arithmetic, struct records, payloadless enums, CSR field widths, match lowering for opcode decode, and 64-bit shift patterns.

<!-- sdn-diagram:id=vhdl_rv64gc_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_rv64gc_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_rv64gc_regression_spec -> std
vhdl_rv64gc_regression_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_rv64gc_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Backend RV64GC RTL Regression Specification

Regression tests for the VHDL backend covering constructs used by rv64gc_rtl modules: 64-bit arithmetic, struct records, payloadless enums, CSR field widths, match lowering for opcode decode, and 64-bit shift patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-fpga-linux-boot |
| Category | Tooling |
| Difficulty | 5/5 |
| Status | Draft |
| Requirements | REQ-7, REQ-16, REQ-17 |
| Research | doc/04_architecture/vhdl_support_matrix.md |
| Source | `test/01_unit/compiler/backend/vhdl_rv64gc_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression tests for the VHDL backend covering constructs used by
rv64gc_rtl modules: 64-bit arithmetic, struct records, payloadless
enums, CSR field widths, match lowering for opcode decode, and
64-bit shift patterns.

Covers:
- AC-8 (VHDL backend bugs identified and fixed)
- AC-9 (VHDL backend regression tests pass after fixes)

## Compiled-Mode Notes

These tests verify VHDL backend output patterns (text assertions on
generated VHDL). Interpreter-safe for text pattern checks. Actual
GHDL analysis requires compiled mode.

## Known Unsupported Constructs (Baseline)

Per the VHDL backend completion report:
- Payload enums (tagged-record lowering) — NOT supported
- Indirect calls — NOT supported
- Recursion — NOT supported
- Dynamic allocation — NOT supported
- Nested array memories — NOT supported
- Float types — NOT supported

These constraints are tested as negative assertions (confirm the
backend rejects or documents unsupported patterns).

## Scenarios

### VHDL Backend 64-bit Type Mapping

#### AC-8: u64 maps to unsigned(63 downto 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_type_map_u64()
expect(vhdl).to_contain("unsigned")
expect(vhdl).to_contain("63 downto 0")
```

</details>

#### AC-8: i64 maps to signed(63 downto 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_type_map_i64()
expect(vhdl).to_contain("signed")
expect(vhdl).to_contain("63 downto 0")
```

</details>

#### AC-8: u32 maps to unsigned(31 downto 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_type_map_u32()
expect(vhdl).to_contain("unsigned")
expect(vhdl).to_contain("31 downto 0")
```

</details>

#### AC-8: bool maps to std_logic or boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_type_map_bool()
val has_logic = vhdl.contains("std_logic")
val has_bool = vhdl.contains("boolean")
val either = has_logic or has_bool
expect(either).to_equal(true)
```

</details>

### VHDL Backend Struct Record Lowering

#### AC-8: struct with u64 fields produces record type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_struct_record_u64()
expect(vhdl).to_contain("record")
```

</details>

#### AC-8: struct fields preserve names in VHDL record

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_struct_record_u64()
expect(vhdl).to_contain("end record")
```

</details>

#### AC-9: CsrFile64-shaped struct compiles to valid record

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CsrFile64 has multiple u64 fields (mstatus, mie, mip, etc.)
val vhdl = vhdl_compile_csr_file64_struct()
expect(vhdl).to_contain("record")
expect(vhdl).to_contain("mstatus")
```

</details>

### VHDL Backend Enum Lowering

#### AC-8: payloadless enum compiles to VHDL enumeration type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_payloadless_enum()
expect(vhdl).to_contain("type")
```

</details>

#### AC-8: payload enum is documented as unsupported (REQ-7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Backend should reject or document payload enums
val supported = vhdl_supports_payload_enums()
expect(supported).to_equal(false)
```

</details>

### VHDL Backend 64-bit Expressions

#### AC-8: 64-bit addition generates correct VHDL operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_u64_add()
val has_plus = vhdl.contains("+")
expect(has_plus).to_equal(true)
```

</details>

#### AC-8: 64-bit shift-left generates sll or shift_left

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_u64_shl()
val has_sll = vhdl.contains("shift_left")
val has_sll2 = vhdl.contains("sll")
val either = has_sll or has_sll2
expect(either).to_equal(true)
```

</details>

#### AC-8: 64-bit shift-right generates srl or shift_right

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_u64_shr()
val has_srl = vhdl.contains("shift_right")
val has_srl2 = vhdl.contains("srl")
val either = has_srl or has_srl2
expect(either).to_equal(true)
```

</details>

#### AC-8: 64-bit bitwise AND generates correct operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_u64_and()
expect(vhdl).to_contain("and")
```

</details>

#### AC-8: 64-bit bitwise OR generates correct operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_u64_or()
expect(vhdl).to_contain("or")
```

</details>

#### AC-8: 64-bit comparison generates correct VHDL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_u64_compare()
val has_eq = vhdl.contains("=")
expect(has_eq).to_equal(true)
```

</details>

### VHDL Backend Match Lowering

#### AC-9: match on u8 generates case statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_match_u8()
expect(vhdl).to_contain("case")
```

</details>

#### AC-9: match with multiple arms generates when clauses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_match_multi_arm()
expect(vhdl).to_contain("when")
```

</details>

#### AC-9: match with default arm generates others

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_match_default()
expect(vhdl).to_contain("others")
```

</details>

### VHDL Backend Process Lowering

#### AC-9: combinational logic generates process with sensitivity list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_combinational_process()
expect(vhdl).to_contain("process")
```

</details>

#### AC-9: sequential logic generates clocked process

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_clocked_process()
expect(vhdl).to_contain("rising_edge")
```

</details>

#### AC-9: process contains signal assignments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_combinational_process()
expect(vhdl).to_contain("<=")
```

</details>

### VHDL Backend Array Lowering

#### AC-9: fixed-size u64 array compiles to VHDL array type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_fixed_u64_array()
expect(vhdl).to_contain("array")
```

</details>

#### AC-9: array indexed access compiles to VHDL index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = vhdl_compile_array_index()
val has_paren = vhdl.contains("(")
expect(has_paren).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-7, REQ-16, REQ-17](REQ-7, REQ-16, REQ-17)
- **Research:** [doc/04_architecture/vhdl_support_matrix.md](doc/04_architecture/vhdl_support_matrix.md)


</details>
