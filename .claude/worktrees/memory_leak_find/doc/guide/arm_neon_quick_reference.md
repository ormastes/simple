# ARM NEON Quick Reference

**Module:** `compiler.backend.native.arm_neon`
**Encoding:** ARMv8-A Advanced SIMD (32-bit instructions)
**Vector Size:** 128-bit (Q registers)

## Register Constants

```simple
use compiler.backend.native.mach_inst.{
    AARCH64_Q0, AARCH64_Q1, AARCH64_Q2, ..., AARCH64_Q15
}
```

**IDs:** 64-79 (Q0-Q15)
**Count:** 16 registers
**Width:** 128-bit (4x32-bit floats, 2x64-bit doubles, 4x32-bit integers)

## Float Operations (f32x4)

| Operation | Function | ARM Instruction | Description |
|-----------|----------|-----------------|-------------|
| **Add** | `encode_fadd_4s(qd, qn, qm)` | `FADD.4S Vd, Vn, Vm` | Vector add (4 floats) |
| **Subtract** | `encode_fsub_4s(qd, qn, qm)` | `FSUB.4S Vd, Vn, Vm` | Vector subtract |
| **Multiply** | `encode_fmul_4s(qd, qn, qm)` | `FMUL.4S Vd, Vn, Vm` | Vector multiply |
| **Divide** | `encode_fdiv_4s(qd, qn, qm)` | `FDIV.4S Vd, Vn, Vm` | Vector divide |
| **Multiply-Add** | `encode_fmla_4s(qd, qn, qm)` | `FMLA.4S Vd, Vn, Vm` | Vd = Vd + Vn * Vm |

## Double Operations (f64x2)

| Operation | Function | ARM Instruction | Description |
|-----------|----------|-----------------|-------------|
| **Add** | `encode_fadd_2d(qd, qn, qm)` | `FADD.2D Vd, Vn, Vm` | Vector add (2 doubles) |
| **Subtract** | `encode_fsub_2d(qd, qn, qm)` | `FSUB.2D Vd, Vn, Vm` | Vector subtract |
| **Multiply** | `encode_fmul_2d(qd, qn, qm)` | `FMUL.2D Vd, Vn, Vm` | Vector multiply |
| **Divide** | `encode_fdiv_2d(qd, qn, qm)` | `FDIV.2D Vd, Vn, Vm` | Vector divide |
| **Multiply-Add** | `encode_fmla_2d(qd, qn, qm)` | `FMLA.2D Vd, Vn, Vm` | Vd = Vd + Vn * Vm |

## Integer Operations (i32x4)

| Operation | Function | ARM Instruction | Description |
|-----------|----------|-----------------|-------------|
| **Add** | `encode_add_4s_int(qd, qn, qm)` | `ADD.4S Vd, Vn, Vm` | Vector add (4 ints) |
| **Subtract** | `encode_sub_4s_int(qd, qn, qm)` | `SUB.4S Vd, Vn, Vm` | Vector subtract |
| **Multiply** | `encode_mul_4s_int(qd, qn, qm)` | `MUL.4S Vd, Vn, Vm` | Vector multiply |

## Load/Store Operations

| Operation | Function | ARM Instruction | Description |
|-----------|----------|-----------------|-------------|
| **Load** | `encode_ldr_q(qd, base, offset)` | `LDR Qd, [Xn, #off]` | Load 128 bits (offset must be multiple of 16) |
| **Store** | `encode_str_q(qs, base, offset)` | `STR Qs, [Xn, #off]` | Store 128 bits |
| **Load Structure** | `encode_ld1_4s(qd, base)` | `LD1 {Vd.4S}, [Xn]` | Load 4 floats (interleaved) |
| **Store Structure** | `encode_st1_4s(qs, base)` | `ST1 {Vs.4S}, [Xn]` | Store 4 floats (interleaved) |

## Horizontal Operations

| Operation | Function | ARM Instruction | Description |
|-----------|----------|-----------------|-------------|
| **Pairwise Add** | `encode_faddp_4s(qd, qn, qm)` | `FADDP.4S Vd, Vn, Vm` | Add adjacent pairs |
| **Max** | `encode_fmaxnm_4s(qd, qn, qm)` | `FMAXNM.4S Vd, Vn, Vm` | Element-wise max (NaN-aware) |
| **Min** | `encode_fminnm_4s(qd, qn, qm)` | `FMINNM.4S Vd, Vn, Vm` | Element-wise min (NaN-aware) |

## Usage Examples

### Vector Addition
```simple
use compiler.backend.native.arm_neon.{encode_fadd_4s}
use compiler.backend.native.mach_inst.{AARCH64_Q0, AARCH64_Q1, AARCH64_Q2}

# Encode: FADD.4S V0, V1, V2
val bytes = encode_fadd_4s(AARCH64_Q0, AARCH64_Q1, AARCH64_Q2)
# Returns: [0x20, 0xD4, 0x22, 0x4E] (4 bytes, little-endian)
```

### Fused Multiply-Add
```simple
use compiler.backend.native.arm_neon.{encode_fmla_4s}

# Encode: FMLA.4S V3, V4, V5  (V3 = V3 + V4 * V5)
val bytes = encode_fmla_4s(AARCH64_Q3, AARCH64_Q4, AARCH64_Q5)
```

### Memory Load
```simple
use compiler.backend.native.arm_neon.{encode_ldr_q}

# Encode: LDR Q0, [X1, #64]
# X1 = base register (GP register ID)
# 64 = offset in bytes (must be multiple of 16)
val bytes = encode_ldr_q(AARCH64_Q0, 1, 64)
```

### Structure Load (AoS)
```simple
use compiler.backend.native.arm_neon.{encode_ld1_4s}

# Encode: LD1 {V2.4S}, [X3]
# Load 4 single-precision floats from memory
# Useful for structure-of-arrays patterns
val bytes = encode_ld1_4s(AARCH64_Q2, 3)
```

## Encoding Details

All NEON instructions are **32-bit fixed-length** (4 bytes):

```
Bits 31-24: Opcode high bits
Bits 23-16: Opcode + Rn field
Bits 15-8:  Opcode + Rd field
Bits 7-0:   Opcode + Rm field + size bits

Rd (bits 0-4):   Destination register (0-15)
Rn (bits 5-9):   First source register (0-15)
Rm (bits 16-20): Second source register (0-15)
```

**Example breakdown (FADD.4S V0, V1, V2):**
```
Base opcode: 0x4E20D400
+ Rd=0:   0x00000000
+ Rn=1:   0x00000020  (1 << 5)
+ Rm=2:   0x00020000  (2 << 16)
= 0x4E22D420

Little-endian bytes: [0x20, 0xD4, 0x22, 0x4E]
```

## Helper Functions

| Function | Purpose |
|----------|---------|
| `q_to_index(q_id)` | Convert Q register ID (64-79) to index (0-15) |
| `arm_neon_reg_name(id)` | Get register name ("q0" - "q15") |
| `neon_encode_f32x4_3reg(opcode, qd, qn, qm)` | Generic 3-register encoding |

## Opcode Constants (mach_inst)

For ISel integration:

```simple
use compiler.backend.native.mach_inst.{
    A64_NEON_FADD_4S,   # f32x4 operations
    A64_NEON_FADD_2D,   # f64x2 operations
    A64_NEON_ADD_4S,    # i32x4 operations
    A64_NEON_LDR_Q,     # Load/store
    A64_NEON_FADDP_4S   # Horizontal ops
}
```

## Limitations

1. **Vector width:** 128-bit only (vs 256-bit AVX2 on x86_64)
2. **Offset alignment:** LDR/STR require 16-byte aligned offsets
3. **Offset range:** Maximum offset = 4095 * 16 = 65520 bytes
4. **Register file:** 16 Q registers (same count as x86_64 YMM)

## Performance Tips

1. **Use FMA:** `FMLA` is faster than separate multiply + add
2. **Prefer structure loads:** `LD1/ST1` for non-contiguous memory access
3. **Minimize load/store:** Keep data in Q registers when possible
4. **Use pairwise ops:** For horizontal reductions (sum, max, min)
5. **Align data:** 16-byte alignment for fastest memory access

## Integration Checklist

For hooking into compiler backend:

- [ ] Add NEON patterns to `isel_aarch64.spl`
- [ ] Map MIR vector ops to NEON opcodes
- [ ] Update register allocator for Q register pool
- [ ] Implement spilling for Q registers (use `STR Q`/`LDR Q`)
- [ ] Add NEON to auto-vectorization pass
- [ ] Test on ARMv8-A hardware or emulator

## See Also

- **Implementation:** `src/compiler/backend/native/arm_neon.spl`
- **Tests:** `test/unit/compiler/arm_neon_spec.spl`
- **Report:** `doc/report/arm_neon_simd_implementation_2026-02-14.md`
- **x86_64 SIMD:** `src/compiler/backend/native/x86_64_simd.spl`
