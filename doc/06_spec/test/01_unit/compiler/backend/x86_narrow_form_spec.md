# X86 Narrow Form Specification

> <details>

<!-- sdn-diagram:id=x86_narrow_form_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_narrow_form_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_narrow_form_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_narrow_form_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 78 | 78 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Narrow Form Specification

## Scenarios

### x86 narrow-form — value_fits_in_i32

#### 0 fits in i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_i32(0)).to_equal(true)
```

</details>

#### 2147483647 (INT32_MAX) fits in i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_i32(2147483647)).to_equal(true)
```

</details>

#### -2147483648 (INT32_MIN) fits in i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_i32(-2147483648)).to_equal(true)
```

</details>

#### 2147483648 (INT32_MAX + 1) does not fit in i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_i32(2147483648)).to_equal(false)
```

</details>

#### -2147483649 (INT32_MIN - 1) does not fit in i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_i32(-2147483649)).to_equal(false)
```

</details>

#### large positive value 9999999999 does not fit in i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_i32(9999999999)).to_equal(false)
```

</details>

### x86 narrow-form — value_fits_in_u32

#### 0 fits in u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_u32(0)).to_equal(true)
```

</details>

#### 4294967295 (UINT32_MAX) fits in u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_u32(4294967295)).to_equal(true)
```

</details>

#### 4294967296 (UINT32_MAX + 1) does not fit in u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_u32(4294967296)).to_equal(false)
```

</details>

#### negative values do not fit in u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_u32(-1)).to_equal(false)
```

</details>

### x86 narrow-form — value_fits_in_32

#### 0 fits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_32(0)).to_equal(true)
```

</details>

#### INT32_MAX fits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_32(2147483647)).to_equal(true)
```

</details>

#### UINT32_MAX fits (via unsigned path)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_32(4294967295)).to_equal(true)
```

</details>

#### UINT32_MAX + 1 does not fit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_32(4294967296)).to_equal(false)
```

</details>

#### INT32_MIN fits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_32(-2147483648)).to_equal(true)
```

</details>

#### INT32_MIN - 1 does not fit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(value_fits_in_32(-2147483649)).to_equal(false)
```

</details>

### x86 narrow-form — imm_fits_sign_extended_32

#### 0 fits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_sign_extended_32(0)).to_equal(true)
```

</details>

#### INT32_MAX fits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_sign_extended_32(2147483647)).to_equal(true)
```

</details>

#### INT32_MAX + 1 does not fit (cannot sign-extend into 64 bits as imm32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_sign_extended_32(2147483648)).to_equal(false)
```

</details>

### x86 narrow-form — imm_fits_in_i8

#### 0 fits in i8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_in_i8(0)).to_equal(true)
```

</details>

#### 127 fits in i8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_in_i8(127)).to_equal(true)
```

</details>

#### -128 fits in i8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_in_i8(-128)).to_equal(true)
```

</details>

#### 128 does not fit in i8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_in_i8(128)).to_equal(false)
```

</details>

#### -129 does not fit in i8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imm_fits_in_i8(-129)).to_equal(false)
```

</details>

### x86 narrow-form — op_preserves_semantics_at_32 approved ops

#### add is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("add")).to_equal(true)
```

</details>

#### sub is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("sub")).to_equal(true)
```

</details>

#### and is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("and")).to_equal(true)
```

</details>

#### or is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("or")).to_equal(true)
```

</details>

#### xor is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("xor")).to_equal(true)
```

</details>

#### mov is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("mov")).to_equal(true)
```

</details>

#### shl is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("shl")).to_equal(true)
```

</details>

#### shr is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("shr")).to_equal(true)
```

</details>

#### sar is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("sar")).to_equal(true)
```

</details>

#### not is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("not")).to_equal(true)
```

</details>

#### neg is safe at 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("neg")).to_equal(true)
```

</details>

#### imul3 is safe at 32-bit (3-operand low-result)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("imul3")).to_equal(true)
```

</details>

### x86 narrow-form — op_preserves_semantics_at_32 rejected ops

#### mul is not safe (unsigned wide result RDX:RAX)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("mul")).to_equal(false)
```

</details>

#### div is not safe (uses RDX:RAX)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("div")).to_equal(false)
```

</details>

#### idiv is not safe (signed wide operands)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("idiv")).to_equal(false)
```

</details>

#### unknown_op is not safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_preserves_semantics_at_32("unknown_op")).to_equal(false)
```

</details>

### x86 narrow-form — op_prohibited_from_narrow

#### mul is prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("mul")).to_equal(true)
```

</details>

#### div is prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("div")).to_equal(true)
```

</details>

#### idiv is prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("idiv")).to_equal(true)
```

</details>

#### rdtsc is prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("rdtsc")).to_equal(true)
```

</details>

#### syscall is prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("syscall")).to_equal(true)
```

</details>

#### add is not prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("add")).to_equal(false)
```

</details>

#### mov is not prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("mov")).to_equal(false)
```

</details>

#### xor is not prohibited

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(op_prohibited_from_narrow("xor")).to_equal(false)
```

</details>

### x86 narrow-form — x86_narrow_form_legal safe rewrites

#### add with value 42 is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("add", 42)).to_equal(true)
```

</details>

#### xor with value 0 is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("xor", 0)).to_equal(true)
```

</details>

#### mov with UINT32_MAX is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("mov", 4294967295)).to_equal(true)
```

</details>

#### and with INT32_MIN is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("and", -2147483648)).to_equal(true)
```

</details>

#### sub with small negative is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("sub", -100)).to_equal(true)
```

</details>

### x86 narrow-form — x86_narrow_form_legal rejected rewrites

#### add with value exceeding UINT32_MAX is illegal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("add", 4294967296)).to_equal(false)
```

</details>

#### mul is always illegal regardless of value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("mul", 1)).to_equal(false)
```

</details>

#### div is always illegal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("div", 1)).to_equal(false)
```

</details>

#### rdtsc is always illegal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("rdtsc", 0)).to_equal(false)
```

</details>

#### mov with value INT32_MIN - 1 is illegal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_form_legal("mov", -2147483649)).to_equal(false)
```

</details>

### x86 narrow-form — x86_narrow_reg_form_legal

#### add with 32-bit src and dst is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_reg_form_legal("add", 32, 32)).to_equal(true)
```

</details>

#### mov with 16-bit src and 32-bit dst is legal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_reg_form_legal("mov", 16, 32)).to_equal(true)
```

</details>

#### add with 64-bit src is illegal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_reg_form_legal("add", 64, 32)).to_equal(false)
```

</details>

#### add with 64-bit dst is illegal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_reg_form_legal("add", 32, 64)).to_equal(false)
```

</details>

#### mul with 32-bit regs is illegal (prohibited op)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_narrow_reg_form_legal("mul", 32, 32)).to_equal(false)
```

</details>

### x86 narrow-form — i386 SysV ABI constants

#### stack alignment is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_stack_align()).to_equal(16)
```

</details>

#### argument slot is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_arg_slot_bytes()).to_equal(4)
```

</details>

#### return register is EAX (register 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_return_reg()).to_equal(0)
```

</details>

#### high return register is EDX (register 2) for 64-bit values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_return_hi_reg()).to_equal(2)
```

</details>

#### all arguments are passed on stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_arg_on_stack(0)).to_equal(true)
expect(i386_sysv_arg_on_stack(5)).to_equal(true)
```

</details>

#### arg0 is at EBP+8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_arg_offset(0)).to_equal(8)
```

</details>

#### arg1 is at EBP+12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_arg_offset(1)).to_equal(12)
```

</details>

#### arg4 is at EBP+24

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_arg_offset(4)).to_equal(24)
```

</details>

#### caller-saved count is 3 (EAX, ECX, EDX)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_caller_saved_count()).to_equal(3)
```

</details>

#### callee-saved count is 4 (EBX, ESI, EDI, EBP)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(i386_sysv_callee_saved_count()).to_equal(4)
```

</details>

### x86 narrow-form — benchmark gate

#### r32 add encoding is shorter than r64 add

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_add_r32_bytes()).to_be_less_than(bench_add_r64_bytes())
```

</details>

#### narrow_form_is_same_or_shorter passes when narrow <= wide

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(narrow_form_is_same_or_shorter(4, 2)).to_equal(true)
expect(narrow_form_is_same_or_shorter(4, 4)).to_equal(true)
```

</details>

#### narrow_form_is_same_or_shorter fails when narrow > wide

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(narrow_form_is_same_or_shorter(2, 4)).to_equal(false)
```

</details>

#### bench_narrow_gate_passes for legal add with small value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("add", 100)).to_equal(true)
```

</details>

#### bench_narrow_gate_passes returns false for prohibited ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("mul", 1)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/x86_narrow_form_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86 narrow-form — value_fits_in_i32
- x86 narrow-form — value_fits_in_u32
- x86 narrow-form — value_fits_in_32
- x86 narrow-form — imm_fits_sign_extended_32
- x86 narrow-form — imm_fits_in_i8
- x86 narrow-form — op_preserves_semantics_at_32 approved ops
- x86 narrow-form — op_preserves_semantics_at_32 rejected ops
- x86 narrow-form — op_prohibited_from_narrow
- x86 narrow-form — x86_narrow_form_legal safe rewrites
- x86 narrow-form — x86_narrow_form_legal rejected rewrites
- x86 narrow-form — x86_narrow_reg_form_legal
- x86 narrow-form — i386 SysV ABI constants
- x86 narrow-form — benchmark gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 78 |
| Active scenarios | 78 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
