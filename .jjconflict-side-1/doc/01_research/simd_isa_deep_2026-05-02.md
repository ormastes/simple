<!-- claude-research -->
# Research: SIMD ISA Deep Detail (2026-05-02, Round 2)

**TL;DR** — This is Round 2 of the SIMD ISA research series for the Simple Language
Compiler. Round 1 (`simd_isa_survey_2026-05-02.md` = Wave A1, breadth-first op
coverage; `simd_internal_state_2026-05-02.md` = Wave A2, repo gap map;
`simd_unified_architecture.md` = Wave B1, type system lock; `simd_backend_strict_emit.md`
= Wave B2, per-ISA op tables) established WHAT ops exist and WHERE gaps are. This
document is DEPTH: exact binary encodings, per-microarch latency tables, intrinsic-name
→ opcode translations, errata corners, and scheduling hazards that backend authors (Wave
C3, strict-emit) and test authors (Wave C4) need to lock byte sequences and validate
correctness. Do not propose Simple-side syntax or encoder helpers here — that is C2/C3
work.

---

## Table of Contents

1. [EVEX Encoding for AVX-512](#1-evex-encoding-for-avx-512)
2. [AArch64 SVE/SVE2 Instruction Encoding](#2-aarch64-svesve2-instruction-encoding)
3. [RVV 1.0 Instruction Encoding + vsetvli Policy](#3-rvv-10-instruction-encoding--vsetvli-policy)
4. [Per-Microarch Latency/Throughput Tables](#4-per-microarch-latencythroughput-tables)
5. [Intrinsic-Name → Opcode Tables](#5-intrinsic-name--opcode-tables)
6. [Undefined Behavior / Errata Corners](#6-undefined-behavior--errata-corners)
7. [Vector Pipeline Hazards and Scheduling](#7-vector-pipeline-hazards-and-scheduling)
8. [F16 / BF16 / INT8 / Mixed-Precision](#8-f16--bf16--int8--mixed-precision)
9. [Cross-ISA Op Semantic Divergences](#9-cross-isa-op-semantic-divergences)
10. [Open Citations Needing Verification](#10-open-citations-needing-verification)

---

## 1. EVEX Encoding for AVX-512

> **Primary reference:** Intel SDM Vol 2A §2.6 (EVEX Prefix Encoding). All bit-level
> claims below are UNVERIFIED via live fetch this round — the Intel SDM was not
> accessible (HTTP 403 on the intrinsics guide; the PDF would need manual download).
> C3 MUST confirm byte sequences against Intel SDM Vol 2A §2.6.1 before locking any
> encoder bytes.

### 1.1 Prefix Overview

EVEX is a mandatory 4-byte prefix used for all AVX-512 instructions. It replaces VEX
(which was 2 or 3 bytes). The first byte is always `0x62`. Unlike the legacy REX prefix
or the 3-byte VEX, EVEX:

- Encodes opmask register (`k0`–`k7`) for per-element predication
- Encodes embedded broadcast (`{1to16}` etc.) via the `b` bit
- Encodes static rounding control / suppress-all-exceptions (SAE) in the `b` + `LL`
  bits when operating on scalar or full-512-bit contexts
- Extends register encoding to 32 vector registers (ZMM0–ZMM31) via `R'`, `X`, `B`
  complement bits

### 1.2 Byte Layout

```
Byte 0: 0x62  (mandatory EVEX escape)

Byte P0 (bits 7..0):
  [7]   ~R    : complement of REX.R (extends ModRM.reg to 4 bits)
  [6]   ~X    : complement of REX.X (extends SIB.index to 4 bits)
  [5]   ~B    : complement of REX.B (extends ModRM.rm/SIB.base to 4 bits)
  [4]   ~R'   : 5th bit of ModRM.reg (ZMM16–31 requires R'=0 i.e. ~R'=1 flipped)
  [3:2] mm    : opcode map select: 01=0F, 10=0F38, 11=0F3A
  [1]   must be 0
  [0]   W     : data element width (for floats: 0=f32, 1=f64; for integers varies)

Byte P1 (bits 7..0):
  [7]   1     : must be 1 (distinguishes EVEX from BOUND instruction)
  [6:3] ~vvvv : complement of source/dest register vvvv (4 bits, as in VEX)
  [2]   1     : must be 1
  [1:0] pp    : implied opcode prefix: 00=none, 01=0x66, 10=0xF3, 11=0xF2

Byte P2 (bits 7..0):
  [7]   z     : zeroing vs merging masking (1=zero, 0=merge)
  [6:5] L'L   : vector length: 00=128-bit (XMM), 01=256-bit (YMM), 10=512-bit (ZMM)
                when b=1 and context is scalar float: L'L encodes static rounding
  [4]   b     : embedded broadcast (mem operand only) or SAE/rounding (reg operand)
  [3]   ~V'   : complement of 5th bit of vvvv (extends vvvv for ZMM16–31 encoding)
  [2:0] aaa   : opmask register selector: 000=k0 (no mask/all-ones), 001–111=k1–k7
```

**UNVERIFIED — confirm against Intel SDM Vol 2A §2.6.1, Table 2-36 (EVEX Prefix
Bit Field Layout).**

### 1.3 Register Encoding

A ZMM register number 0..31 is encoded using a 5-bit field split across prefix bits:

```
ZMM register N:
  bit4 = ~R' in P0[4]   (most significant)
  bit3 = ~R  in P0[7]
  bits[2:0] in ModRM.reg[2:0]
  
  For a destination in ModRM.rm (SIB/memory operand context):
  bit4 = ~B  in P0[5]
  bit3 = (extra bit from P0[5] extended path)
  bits in ModRM.rm[2:0]
```

All complement bits: a bit value of 0 in the prefix means 1 in the logical register
field (inverted sense inherited from REX convention). **UNVERIFIED — confirm §2.6.1.**

### 1.4 Opmask (k) Encoding

- `aaa` = 000: k0, which is the "no-mask" sentinel — all elements active, merge mode
  implied (the z-bit is ignored when aaa=000 per §2.6.1 note)
- `aaa` = 001..111: k1–k7 active; z-bit selects zero vs merge behavior for inactive lanes
- An instruction referencing k0 explicitly (e.g., `KMOVW k0, eax`) uses a non-EVEX path
- **UNVERIFIED — confirm the k0 sentinel behavior against Intel SDM §2.6.1.**

### 1.5 Embedded Broadcast

When `b=1` and the second operand is a memory reference (ModRM indicates memory), the
single memory element is broadcast to fill all active lanes. The broadcast factor depends
on L'L and W:

| L'L | W | Broadcast factor |
|-----|---|-----------------|
| 10  | 0 | {1to16} — 16 f32 elements from a 4-byte load |
| 10  | 1 | {1to8}  — 8 f64 elements from an 8-byte load |
| 01  | 0 | {1to8}  — 8 f32 from 4-byte load (YMM context with VL) |
| 01  | 1 | {1to4}  — 4 f64 from 8-byte load |

**UNVERIFIED — confirm broadcast factors against Intel SDM Vol 2A §2.6.1, Table 2-38.**

### 1.6 Static Rounding / SAE Encoding

When `b=1` and both operands are registers (ModRM does NOT indicate memory), the `b` bit
encodes SAE (suppress all exceptions) or static rounding:

- L'L = 00 + b=1: `{rn-sae}` — round-to-nearest, suppress exceptions
- L'L = 01 + b=1: `{rd-sae}` — round-down (toward −∞)
- L'L = 10 + b=1: `{ru-sae}` — round-up (toward +∞)
- L'L = 11 + b=1: `{rz-sae}` — round-toward-zero (truncate)

Note: The actual vector length for register-register 512-bit ops is implicitly ZMM (512
bits) when rounding override is active — L'L does not change the register width here, it
is repurposed as the rounding mode selector. **UNVERIFIED — confirm §2.6.1.**

### 1.7 Worked Example: `vfmadd213ps zmm1{k1}{z}, zmm2, zmm3 {rn-sae}`

Assembly: fused multiply-add, form 213 (src1 × dest + src3 → dest), f32 lanes, ZMM,
zeroing opmask k1, round-nearest with SAE.

```
Semantic: zmm1[i] = (zmm2[i] × zmm1[i]) + zmm3[i], if k1[i] else 0
Encoding intent (all UNVERIFIED — verify against Intel SDM §2.6.1 + §3.x entry for VFMADD213PS):

  Byte 0: 0x62          (EVEX escape)
  Byte P0: derived from:
    ~R  = 1 (zmm1 is reg < 8, no extension needed for ModRM.reg)
    ~X  = 1 (no SIB index extension)
    ~B  = 1 (zmm3 rm-side, reg < 8)
    ~R' = 1 (zmm1 bit4 = 0, ~R'=1)
    mm  = 10 (opcode map 0F38)
    W   = 0  (f32)
    → P0 = 0b_1111_10_0_0 = 0xF2  (UNVERIFIED)
  Byte P1:
    must-1 bit = 1
    ~vvvv for zmm2 source = ~(0010) = 1101
    must-1 bit = 1
    pp = 01 (0x66 prefix for packed f32)
    → P1 = 0b_1_1101_1_01 = 0xED  (UNVERIFIED)
  Byte P2:
    z   = 1   (zeroing mask)
    L'L = 10  (512-bit ZMM) — BUT: rn-sae overrides L'L to 00 with b=1
            → for rn-sae: L'L=00, b=1
    L'L = 00, b = 1  → P2[6:4] = 0_0_1
    ~V' = 1   (zmm2 vvvv 5th bit = 0, ~V'=1)
    aaa = 001 (k1)
    → P2 = 0b_1_00_1_1_001 = 0x99  (UNVERIFIED)
  Opcode byte: 0xA8 (VFMADD213PS opcode in map 0F38)  (UNVERIFIED)
  ModRM: mod=11 (reg-reg), reg=zmm1 id, rm=zmm3 id
```

**C3 ACTION REQUIRED: Verify this byte sequence against Intel SDM Vol 2A §2.6 and the
individual opcode entry for VFMADD213PS in §3.5.x before encoding.**

### 1.8 VFMADD Forms: 132 / 213 / 231

AVX-512 FMA has three forms that differ in which register is overwritten (the
accumulator) and which roles the operands play:

| Form | Formula | dest overwritten |
|------|---------|-----------------|
| VFMADD132PS dst, src1, src2 | dst = (dst × src2) + src1 | dst |
| VFMADD213PS dst, src1, src2 | dst = (src1 × dst) + src2 | dst |
| VFMADD231PS dst, src1, src2 | dst = (src1 × src2) + dst | dst |

The "3-digit suffix" is a mnemonic: first digit = which argument is src1 for multiply,
second digit = which argument is the addend, third digit = implicit. In 213: arg2 × arg1
+ arg3 = result written to arg1. Choosing the wrong form silently reorders
multiplier/addend without causing a trap. See §6 errata item 6-E for consequences.

---

## 2. AArch64 SVE/SVE2 Instruction Encoding

> **Primary reference:** Arm Architecture Reference Manual for A-profile (ARMv9)
> Chapter C7 (SVE Instructions), §C7.2.x per-instruction entries. ARM developer pages
> returned 0 bytes (JS-rendered portal). All encoding bit claims below are UNVERIFIED
> via live fetch — C3 must verify against the ARMv9 ARM PDF before locking encoder bytes.
> Section numbers given are per the ARMv9 ARM §C7.2 layout convention.

### 2.1 A64 32-bit Instruction Word Format for SVE

All A64 instructions are 32-bit fixed-width. SVE instructions occupy the op-group
range `0x04xxxxxx` (bits [31:24] = 0b_0000_0100 for most SVE arithmetic). The exact
top-byte varies by instruction class:

```
SVE instruction generic layout (varies per class):

Bits [31:24]: op group / major opcode
  0x04: SVE integer/FP arithmetic (most FADD, FMUL, FMLA etc.)
  0x05: SVE memory (LD1, ST1, prefetch variants)
  0x25: SVE predicate operations (PTRUE, PFALSE, PNEXT, etc.)
  0x04 with bits [23:22] distinguishing predicated vs. unpredicated

Bits [23:22]: variant selector (predicated/unpredicated, widening, etc.)
Bits [21:20]: element size: 00=B(8-bit), 01=H(16-bit), 10=S(32-bit), 11=D(64-bit)
Bits [19:16]: predicate register Pg (4 bits, P0–P15)
Bits [15:13]: further opcode sub-type
Bit  [12]:   Merging (M) vs Zeroing (Z) predication in the /M, /Z suffix
Bits [11:10]: further opcode
Bits [9:5]:  source register Zn (5 bits, Z0–Z31)
Bits [4:0]:  destination register Zd (5 bits, Z0–Z31)
```

**UNVERIFIED — confirm bit field positions against ARMv9 ARM §C7.1 (SVE encoding
overview). The exact grouping differs between arithmetic and memory encodings.**

### 2.2 Predicate Register Field: Governing Predicate Pg

The governing predicate `Pg` is a 4-bit field (P0–P15). It appears at a fixed location
within SVE arithmetic instructions to identify which predicate register controls which
lanes are active. The field is labeled `Pg` (governing = the predicate that controls
masking) vs `Pn`/`Pm` (source predicates used as operands in predicate operations).

Key encoding rules (UNVERIFIED — §C7.1):
- Pg field: bits [19:16] in most SVE arithmetic instructions
- The `/M` (merging) vs `/Z` (zeroing) modifier is encoded in bit [13] or [16] depending
  on instruction class — this is the key predication flavor selector
- P15 is architecturally reserved for specific uses; ACLE §11.1 convention forbids
  general allocation (Wave B2 §4.5 documents this as "P15 reserved")
- p0 conventional all-true governing predicate for unconditional ops

### 2.3 Predicate Patterns (for PTRUE / WHILELT / WHILELO etc.)

When generating a predicate via `PTRUE` or `WHILELT`, a "predicate pattern" immediate
selects which lanes are set true:

| Pattern name | Encoding (5-bit imm) | Meaning |
|---|---|---|
| POW2   | 00000 | Largest power-of-2 vector length ≤ VL |
| VL1    | 00001 | VL = 1 element |
| VL2    | 00010 | VL = 2 elements |
| VL3    | 00011 | VL = 3 elements |
| VL4    | 00100 | VL = 4 elements |
| VL5    | 00101 | VL = 5 elements |
| VL6    | 00110 | VL = 6 elements |
| VL7    | 00111 | VL = 7 elements |
| VL8    | 01000 | VL = 8 elements |
| VL16   | 01001 | VL = 16 elements |
| VL32   | 01010 | VL = 32 elements |
| VL64   | 01011 | VL = 64 elements |
| VL128  | 01100 | VL = 128 elements |
| VL256  | 01101 | VL = 256 elements |
| MUL4   | 11101 | Largest multiple of 4 ≤ VL |
| MUL3   | 11110 | Largest multiple of 3 ≤ VL |
| ALL    | 11111 | All elements (full VL) |

**UNVERIFIED — confirm 5-bit encoding values against ARMv9 ARM §C1.3.2 (SVE
predicate pattern). Pattern `ALL` = 31 = 0b11111 is widely documented as correct.**

### 2.4 Encoding Example: `FADD Z0.S, P0/M, Z0.S, Z1.S`

SVE predicated FADD, merging predicate P0, f32 elements, dest Z0, sources Z0 and Z1.

```
32-bit word (UNVERIFIED — verify against ARMv9 ARM §C7.2.57 FADD (vectors)):

bits [31:24] = 0x65   (SVE FP arithmetic group, .S = bits[23:22]=10 = 32-bit)
bits [23:22] = 10     (size = S = f32)
bits [21:16] = 000000 (sub-opcode for FADD, merging form — UNVERIFIED specific value)
bits [15:13] = 000    (further opcode field)
bit  [12]    = 1      (merging /M predication)
bits [11:10] = 00     (further opcode)
bits [9:5]   = 00001  (Zn = Z1, 5-bit)
bits [19:16] = 0000   (Pg = P0, 4-bit)
bits [4:0]   = 00000  (Zd = Z0, 5-bit)

Assembly mnemonic:  FADD Z0.S, P0/M, Z0.S, Z1.S
ACLE intrinsic:     svadd_f32_m(p0, z0, z1)
```

**C3 ACTION REQUIRED: Verify §C7.2.57 FADD (vectors) entry in ARMv9 ARM for exact
bit positions before encoding.**

### 2.5 Encoding Example: `FMLA Z0.S, P0/M, Z1.S, Z2.S`

SVE predicated FMLA (fused multiply-add, dest accumulates):

```
32-bit word (UNVERIFIED — verify ARMv9 ARM §C7.2.74 FMLA (vectors)):

The FMLA instruction for SVE has the form:
  Zda[i] = Zda[i] + Zn[i] * Zm[i]   (where active per Pg)

bits [31:24]: 0x65 (SVE FP arithmetic)
bits [23:22]: 10   (size = S = f32)
...intermediate bits encode FMLA opcode...
bits [19:16]: Pg (governing predicate)
bits [9:5]:   Zn (first source)
bits [4:0]:   Zda (dest/accumulator)
An additional Zm field encodes the second source — exact bit position UNVERIFIED.

ACLE intrinsic: svmla_f32_m(p0, z0, z1, z2)
```

### 2.6 PSTATE Interaction with Predicate Test Instructions

SVE predicate-test instructions (`PTEST`, `PTRUE`, `WHILE*`) write to NZCV flags:

| NZCV bit | Meaning when set |
|---|---|
| N (negative) | First active element has its sign bit set |
| Z (zero)     | No active element is true (all inactive / all false predicate) |
| C (carry)    | Not last active element; i.e., there are more elements to process |
| V (overflow) | (Unused / zero for predicate tests) |

The most important loop-control use:
- After `WHILELT p0.s, x0, x1`, check `b.first` (branch-if-not-last) to continue the
  strip-mining loop. `b.first` tests that C=1 (not-last active element).
- Check `b.none` (branch-if-Z=1) to skip a loop body if no elements are active.
- `PTEST pg, pn.b` explicitly sets NZCV from predicate content.

**Reference: ARMv9 ARM §C1.2.4 (Condition flags set by SVE predicate tests). UNVERIFIED
exact sub-section number.**

### 2.7 SVE2 Extensions vs SVE

SVE2 is mandatory in Armv9 (optional in Armv8). SVE2 adds:
- `SQDMULH` / `SQRDMULH`: saturating doubling multiply-high
- `SABALB` / `SABALT`: absolute difference and accumulate (low/high)
- `MATCH` / `NMATCH`: 8-bit element matching across vector (useful for string ops)
- `LDNT1*` / `STNT1*`: non-temporal scatter/gather
- BF16 extensions (`BFCVT`, `BFDOT`, `BFMMLA`) — see §8

SVE2 reuses the same predicate and vector register layout as SVE. All SVE encoding
ranges are a strict subset of SVE2; SVE2 adds new instruction encodings without
changing existing ones.

---

## 3. RVV 1.0 Instruction Encoding + vsetvli Policy

> **Primary reference:** RISC-V "V" Vector Extension v1.0 (archived at
> github.com/riscvarchive/riscv-v-spec). Sections cited are from the live-fetched
> spec and are HIGH CONFIDENCE. Bit-level encoding details from the adoc source are
> confirmed via direct fetch of inst-table.adoc and v-spec.adoc.

### 3.1 Opcode Space (RVV 1.0 §5)

RVV 1.0 instructions occupy three major opcode groups (RISC-V 7-bit opcode field):

| Major opcode | Binary      | RISC-V name | Use |
|---|---|---|---|
| LOAD-FP  | 0000111 | LOAD-FP  | Vector loads (VL*, VLS*, VLX*) |
| STORE-FP | 0100111 | STORE-FP | Vector stores (VS*, VSS*, VSX*) |
| OP-V     | 1010111 | OP-V     | All vector arithmetic + config |

The `funct3` field within OP-V selects the sub-encoding category. Per RVV §10.1 Table 13:

| funct3[2:0] | Name   | Operands        | Scalar src type |
|---|---|---|---|
| 000         | OPIVV  | vector-vector   | N/A             |
| 001         | OPFVV  | vector-vector   | N/A (FP)        |
| 010         | OPMVV  | vector-vector   | N/A (mask/int)  |
| 011         | OPIVI  | vector-imm      | 5-bit imm       |
| 100         | OPIVX  | vector-scalar   | GPR x register  |
| 101         | OPFVF  | vector-scalar   | FP f register   |
| 110         | OPMVX  | vector-scalar   | GPR x register  |
| 111         | OPCFG  | config (scalars/imms) | see §6   |

Source: RVV spec §10.1.

### 3.2 OPCFG (vsetvli / vsetivli / vsetvl) Encoding

The `OPCFG` funct3=111 sub-group encodes all three configuration instructions. The
31-bit layout (beyond the 7-bit opcode) distinguishes them by the top bits of the
12-bit immediate / rs2 field (per RVV §6 + vcfg-format.adoc):

```
vsetvli  rd, rs1, zimm11:
  [31]    = 0
  [30:20] = zimm[10:0]  (vtype immediate, 11 bits)
  [19:15] = rs1
  [14:12] = 111  (funct3 = OPCFG)
  [11:7]  = rd
  [6:0]   = 1010111 (OP-V)

vsetivli rd, uimm5, zimm10:
  [31:30] = 11
  [29:20] = zimm[9:0]   (vtype immediate, 10 bits)
  [19:15] = uimm[4:0]   (immediate AVL, 5 bits)
  [14:12] = 111  (funct3 = OPCFG)
  [11:7]  = rd
  [6:0]   = 1010111 (OP-V)

vsetvl rd, rs1, rs2:
  [31:25] = 1000000
  [24:20] = rs2
  [19:15] = rs1
  [14:12] = 111  (funct3 = OPCFG)
  [11:7]  = rd
  [6:0]   = 1010111 (OP-V)
```

**PARTIALLY VERIFIED via vcfg-format.adoc. The top-bit disambiguation (bit 31=0 for
vsetvli, bits 31:30=11 for vsetivli, bits 31:25=1000000 for vsetvl) is per RVV §6.**

### 3.3 vtype Register Layout (RVV §3.4)

The `vtype` CSR is XLEN bits wide. Field layout (from vtype-format.adoc, live-fetched):

| Bit(s)     | Field      | Meaning |
|---|---|---|
| XLEN-1     | vill       | Illegal vtype — set when configuration unsupported |
| XLEN-2:8   | reserved   | Must be zero; non-zero → vill set |
| 7          | vma        | Vector Mask Agnostic (1=agnostic, 0=undisturbed) |
| 6          | vta        | Vector Tail Agnostic (1=agnostic, 0=undisturbed) |
| 5:3        | vsew[2:0]  | Selected Element Width |
| 2:0        | vlmul[2:0] | Vector Length MULtiplier |

Source: RVV §3.4.

### 3.4 vsew[2:0] Encoding (RVV §3.4.1)

| vsew[2:0] | SEW |
|---|---|
| 000 | 8 bits |
| 001 | 16 bits |
| 010 | 32 bits |
| 011 | 64 bits |
| 1xx | Reserved |

Source: RVV §3.4.1 Table 2.

### 3.5 vlmul[2:0] Encoding (RVV §3.4.2)

| vlmul[2:0] | Assembler | LMUL | Meaning |
|---|---|---|---|
| 000 | m1   | 1     | 1 register per group |
| 001 | m2   | 2     | 2 registers per group |
| 010 | m4   | 4     | 4 registers per group |
| 011 | m8   | 8     | 8 registers per group |
| 100 | reserved | — | |
| 101 | mf8  | 1/8   | Fractional: 1/8 register |
| 110 | mf4  | 1/4   | Fractional: 1/4 register |
| 111 | mf2  | 1/2   | Fractional: 1/2 register |

Note: encoding 100 is reserved per spec (no standard fractional mf16 defined).
Source: RVV §3.4.2 (UNVERIFIED for exact binary bit assignments 101/110/111;
the assembler mnemonics mf8/mf4/mf2 are confirmed by §6.1).

### 3.6 vta / vma Policy (RVV §3.4.3)

| vta | vma | Tail elements | Inactive (masked-off) elements |
|---|---|---|---|
| 0 | 0 | undisturbed | undisturbed |
| 0 | 1 | undisturbed | agnostic (may write 1s) |
| 1 | 0 | agnostic    | undisturbed |
| 1 | 1 | agnostic    | agnostic (preferred for performance) |

**Agnostic**: elements may retain old value OR be overwritten with all-1s — implementation
choice, neither is guaranteed. This means code MUST NOT read destination lanes that are
tail/masked-agnostic and expect a specific value.

**Undisturbed**: elements retain their previous value exactly.

The backend default (Wave B2 §4.6) is `ta, ma` (vta=1, vma=1) to maximize throughput.
If the abstract op guarantees zero-fill for inactive lanes (Wave B1 §4.2 default), the
backend must emit an explicit `vmv.v.i vd, 0` before the masked operation when vma=1,
then do the masked operation with mask undisturbed style — or use vma=0 (mu).

Source: RVV §3.4.3, confirmed live.

### 3.7 vill Behavior (RVV §3.4.4 + §6.1.1)

- `vill` is bit XLEN-1 of `vtype` (sign bit in XLEN-wide CSR).
- Set by hardware when `vsetvli` receives an unsupported vtype value.
- When `vill=1`: ANY vector instruction that depends on `vtype` raises
  illegal-instruction exception. `vset{i}vl{i}` and whole-register loads/stores
  do NOT depend on vtype and may still execute.
- Software should check `vill` after each `vsetvli` when probing configuration support.

Source: RVV §3.4.4, §6.1.1, confirmed live.

### 3.8 vstart CSR (RVV §3.7)

- `vstart` specifies the index of the FIRST element to execute in the next vector
  instruction.
- Normally only written by hardware on a trap (synchronous exception or async interrupt)
  on a vector instruction. The element index where the trap occurred is saved.
- After a resumable trap handler returns, the vector instruction resumes from `vstart`.
- All vector instructions reset `vstart` to 0 on completion (including `vset{i}vl{i}`).
- `vstart` is NOT modified when the instruction raises illegal-instruction exception.

See §6 errata for the non-obvious behavior when `vstart != 0` at instruction entry.
Source: RVV §3.7, confirmed live.

### 3.9 Key Arithmetic Instruction funct6 Assignments (§10 + inst-table.adoc)

The 6-bit `funct6` field selects the specific operation within OPFVV/OPFVF/OPIVV etc.
Key FP assignments (OPFVV = funct3=001, OPFVF = funct3=101):

| funct6 | OPFVV mnemonic | OPFVF mnemonic |
|---|---|---|
| 000000 | vfadd.vv  | vfadd.vf  |
| 000010 | vfsub.vv  | vfsub.vf  |
| 000100 | vfmin.vv  | vfmin.vf  |
| 000110 | vfmax.vv  | vfmax.vf  |
| 001000 | vfsgnj.vv | vfsgnj.vf |
| 010000 | vfmul.vv  | vfmul.vf  |
| 011000 | vfmacc.vv | vfmacc.vf  |  ← vd += vs1 * vs2
| 011001 | vfnmacc.vv| vfnmacc.vf |
| 011010 | vfmsac.vv | vfmsac.vf  |
| 011011 | vfnmsac.vv| vfnmsac.vf |
| 011100 | vfmadd.vv | vfmadd.vf  |  ← vd = vs1 * vd + vs2
| 011101 | vfnmadd.vv| vfnmadd.vf |
| 011110 | vfmsub.vv | vfmsub.vf  |
| 011111 | vfnmsub.vv| vfnmsub.vf |
| 100000 | vfredosum.vs (ordered reduction) | |
| 000001 | vfredusum.vs (unordered reduction) | |

Source: inst-table.adoc (live-fetched), cross-checked with §14 (vector FP instructions).
**PARTIALLY VERIFIED — funct6 binary values confirmed from table; some entries
UNVERIFIED against the authoritative RVV spec PDF.**

### 3.10 Worked Examples

```
# Set VL for f32, LMUL=1, tail agnostic, mask agnostic
vsetvli t0, a0, e32, m1, ta, ma
# t0 = number of f32 elements hardware will process this iteration
# a0 = requested element count (AVL)
# vtype = { vill=0, vma=1, vta=1, vsew=010 (32b), vlmul=000 (m1) }

# Vector FP add: v8[i] = v0[i] + v4[i], masked by v0.t (mask register v0)
vfadd.vv v8, v0, v4, v0.t
# funct6=000000, funct3=001 (OPFVV), vm=0 (mask enabled), vd=v8, vs1=v0, vs2=v4
# mask register is always v0 when vm=0

# FMA accumulate: v8[i] += v4[i] * v8[i]  (overwrites multiplicand)
vfmacc.vv v8, v4, v8
# (without mask, vm=1 = no mask / all active)
```

### 3.11 Fractional LMUL Use Cases

Fractional LMUL (mf2, mf4, mf8) reduces the number of vector register bits used,
enabling more independent register groups for narrow types in mixed-width code:

```
# Processing i8 and i32 together: use mf4 for i32 so both use same logical element count
vsetvli t0, a0, e8, m1, ta, ma    # i8 LMUL=1: 16 elements per VLEN=128
vsetvli t0, a0, e32, mf4, ta, ma  # i32 mf4: same 16 elements but 1/4 register
```

The backend currently always uses LMUL=1 (Wave B2 §4.6 default). Fractional LMUL is
reserved for future widening/narrowing op support.

---

## 4. Per-Microarch Latency/Throughput Tables

> **IMPORTANT:** The Agner Fog instruction tables PDF and uops.info HTML both failed to
> fetch as parseable text this round (binary PDF / JS-rendered HTML). Numbers below are
> UNVERIFIED reconstructions from training knowledge. C3/C4 MUST verify each row against:
> - Agner Fog "Instruction Tables" (PDF, latest edition from agner.org/optimize)
> - uops.info XML (instructions.xml, March 2026 edition)
> - Intel 64 and IA-32 Architectures Optimization Reference Manual (§A for throughput)
> - Arm Cortex-X4 Software Optimization Guide
> Every row is tagged [UNVERIFIED] until a human or automated check confirms.

### 4.1 Intel Skylake-X (SKX) / Ice Lake (ICL) / Sapphire Rapids (SPR): AVX-512

Notation: Lat = latency cycles, TP = throughput (instructions/cycle), Ports = execution ports.

| Op | Variant | SKX Lat | SKX TP | SKX Ports | ICL Lat | ICL TP | SPR Lat | SPR TP | Notes |
|---|---|---|---|---|---|---|---|---|---|
| VADDPS ZMM | zmm,zmm,zmm | 4 | 0.5 | p0/p1 | 4 | 0.5 | 4 | 1.0 | [UNVERIFIED] |
| VMULPS ZMM | zmm,zmm,zmm | 4 | 0.5 | p0/p1 | 4 | 0.5 | 4 | 1.0 | [UNVERIFIED] |
| VFMADD213PS ZMM | zmm,zmm,zmm | 4 | 0.5 | p0/p1 | 4 | 0.5 | 4 | 1.0 | [UNVERIFIED] |
| VPERMT2PS ZMM | zmm,zmm,zmm | 3 | 1.0 | p5 | 3 | 1.0 | 3 | 1.0 | [UNVERIFIED] |
| VGATHERDPS ZMM | k,zmm,m32 | ~20 | ~20 | p2/p3 | ~20 | ~12 | ~16 | ~10 | High variability [UNVERIFIED] |
| VSCATTERDPS | m32,k,zmm | ~20 | ~20 | p2/p3/p7 | ~26 | ~26 | ~20 | ~20 | Conflict penalty; see §6 [UNVERIFIED] |
| VMOVAPS ZMM load | zmm,[m] | 6 | 0.5 | p2/p3 | 6 | 0.5 | 6 | 0.5 | L1 hit [UNVERIFIED] |
| VMOVAPS ZMM store | [m],zmm | 4 | 1.0 | p7 | 4 | 1.0 | 4 | 1.0 | [UNVERIFIED] |
| KANDW | k,k,k | 1 | 0.33 | p0/p1/p5 | 1 | 0.33 | 1 | 0.33 | [UNVERIFIED] |
| VPCMPEQD ZMM | k,zmm,zmm | 3 | 0.5 | p0/p1 | 3 | 0.5 | 3 | 1.0 | [UNVERIFIED] |

**SKX note**: On Skylake-X, running 512-bit (ZMM) instructions causes a frequency
downclocking event ("heavy AVX-512") that persists for hundreds of cycles after the last
ZMM use. This penalty is separate from per-instruction latency. See §7.1.

**ICL note**: Ice Lake introduced a second 512-bit FMA unit (two ZMM FMA ports),
doubling FMA throughput vs SKX's single port. TP 0.5 means two operations per cycle.

**SPR note**: Sapphire Rapids added AVX-512-FP16 and AMX tile operations; FMA TP
improved; ZMM no longer causes frequency downclocking on SPR. [UNVERIFIED for SPR
downclocking abolition — verify against Intel SPR datasheet.]

### 4.2 AMD Zen 4: AVX-512 (Double-Pumped on 256-bit ALU)

| Op | Variant | Zen4 Lat | Zen4 TP | Notes |
|---|---|---|---|---|
| VADDPS ZMM | zmm,zmm,zmm | 4 | 0.5 | Two 256-bit passes internally [UNVERIFIED] |
| VMULPS ZMM | zmm,zmm,zmm | 4 | 0.5 | Double-pump [UNVERIFIED] |
| VFMADD213PS ZMM | zmm,zmm,zmm | 4 | 0.5 | [UNVERIFIED] |
| VADDPS YMM | ymm,ymm,ymm | 4 | 0.25 | Single-pass; same latency [UNVERIFIED] |
| VMOVAPS ZMM load | zmm,[m] | 7 | 0.5 | L1 hit [UNVERIFIED] |
| VPCMPEQD ZMM | k,zmm,zmm | 4 | 0.5 | [UNVERIFIED] |

**Zen 4 "double-pump" explanation**: Zen 4 implements AVX-512 by executing two 256-bit
μops per 512-bit instruction. The physical ALU is 256 bits wide. Consequence: a 512-bit
VFMADD has latency equal to a 256-bit VFMADD (they share the same execution unit, just
two μops sequenced), but uses 2 decode slots. The backend should prefer 256-bit ops on
Zen 4 when the operation count is small (fewer μop slots consumed). For large loop
bodies, 512-bit is usually still better due to halving loop iterations.

**Reference**: "AMD Zen 4 Microarchitecture Analysis" — UNVERIFIED for cycle counts;
Agner Fog Zen4 section is the primary source C3 should consult.

### 4.3 Apple M-Series / Cortex-X: NEON 128-bit

| Op | Variant | M2 Lat | M2 TP | Cortex-X3 Lat | Cortex-X3 TP | Notes |
|---|---|---|---|---|---|---|
| FMLA V.4S | q,q,q | 4 | 0.25 | 3 | 0.33 | [UNVERIFIED] |
| FMUL V.4S | q,q,q | 4 | 0.25 | 3 | 0.33 | [UNVERIFIED] |
| FADD V.4S | q,q,q | 3 | 0.25 | 3 | 0.33 | [UNVERIFIED] |
| LD1 {V.4S} | [x0]  | 4 | 0.33 | 4 | 0.33 | L1 hit [UNVERIFIED] |
| ST1 {V.4S} | [x0]  | 1 | 0.33 | 1 | 0.5  | [UNVERIFIED] |
| TBL V.16B | q,{q},q | 2 | 0.5 | 3 | 1.0 | [UNVERIFIED] |
| TBX V.16B | q,{q},q | 2 | 0.5 | 3 | 1.0 | [UNVERIFIED] |

**M-chip note**: Apple M-series microarchitecture is not publicly documented. Numbers
marked UNVERIFIED are training-data estimates. Dougall Johnson's "Apple M1 uarch
exploration" (https://dougallj.github.io/applecpu/firestorm.html) is the closest public
source. C3 should verify against that source.

**Cortex-X note**: ARM Software Optimization Guide for Cortex-X3 (reference:
ARM107709, DEN0138) is the primary source. C4 should run microbenchmarks on target HW.

### 4.4 Cortex-A510 / A715: SVE2 (128-bit and 256-bit VL variants)

| Op | Variant | A510 Lat | A510 TP | A715 Lat | A715 TP | Notes |
|---|---|---|---|---|---|---|
| FADD Zd.S | z,pg/m,z,z | 3 | 1.0 | 3 | 0.5 | [UNVERIFIED] |
| FMLA Zd.S | z,pg/m,z,z | 4 | 1.0 | 4 | 0.5 | [UNVERIFIED] |
| LD1W | {z},[x,z] | 4-6 | 1.0 | 4-6 | 0.5 | L1 hit [UNVERIFIED] |
| PTRUE | p.s, ALL | 1 | 1.0 | 1 | 1.0 | [UNVERIFIED] |
| PTEST | p,p.b | 1 | 1.0 | 1 | 0.5 | [UNVERIFIED] |
| WHILELT | p.s,x,x | 2 | 1.0 | 2 | 1.0 | [UNVERIFIED] |

**A510**: In-order micro-architecture. A715: Out-of-order.
**Primary source**: ARM Cortex-A510/A715 Software Optimization Guide — UNVERIFIED.

### 4.5 SiFive P670 / Andes AX65: RVV 1.0

| Op | LMUL | VLEN | P670 Lat (est) | P670 TP | AX65 Lat (est) | AX65 TP | Notes |
|---|---|---|---|---|---|---|---|
| vfadd.vv | m1 | 128 | 4 | 1.0 | 4 | 1.0 | [UNVERIFIED] |
| vfmacc.vv | m1 | 128 | 4 | 1.0 | 5 | 1.0 | [UNVERIFIED] |
| vsetvli | — | — | 1-2 | — | 1-2 | — | Not free [UNVERIFIED] |
| vle32.v | m1 | 128 | 4-6 | 1.0 | 4-6 | 1.0 | L1 hit [UNVERIFIED] |
| vmseq.vv | m1 | 128 | 2 | 1.0 | 2 | 1.0 | [UNVERIFIED] |
| vmv.v.i | m1 | — | 1 | 1.0 | 1 | 1.0 | [UNVERIFIED] |

**Primary sources** (UNVERIFIED this round):
- SiFive P670 Core Complex Manual (latest, sifive.com)
- Andes AX65 Processor Datasheet (andestech.com)
- "RISC-V Vector Extension on SiFive Performance Cores" — SiFive blog

---

## 5. Intrinsic-Name → Opcode Tables

> These tables map the 30 abstract Vector trait ops from Wave B1 §3.1 to per-ISA
> intrinsic names and underlying machine opcodes. The abstract op names are those used
> in the Simple compiler's MIR. Intrinsic name accuracy for Intel is based on Intel
> Intrinsics Guide format (intrinsics-guide.intel.com, UNVERIFIED via fetch — 403);
> ARM ACLE names from arm_neon.h / arm_sve.h conventions; RVV names from
> rvv-intrinsic-doc (github.com/riscv-non-isa/rvv-intrinsic-doc).

### 5.1 Intel Intrinsics: `_mm512_*` / `_mm256_*` / `_mm_*`

For f32 element type (suffix `_ps`). YMM = _mm256_, ZMM = _mm512_.

| Abstract Op | Intel ZMM Intrinsic | Machine Opcode |
|---|---|---|
| add        | `_mm512_add_ps(a,b)` | VADDPS zmm,zmm,zmm/m512/m32bcst |
| sub        | `_mm512_sub_ps(a,b)` | VSUBPS zmm,zmm,zmm/m512 |
| mul        | `_mm512_mul_ps(a,b)` | VMULPS zmm,zmm,zmm/m512 |
| div        | `_mm512_div_ps(a,b)` | VDIVPS zmm,zmm,zmm/m512 |
| fma (213)  | `_mm512_fmadd_ps(a,b,c)` | VFMADD213PS zmm,zmm,zmm/m512 |
| fma (231)  | `_mm512_fmadd_ps(a,b,c)` (same) | VFMADD231PS (compiler selects form) |
| sqrt       | `_mm512_sqrt_ps(a)` | VSQRTPS zmm,zmm/m512 |
| min        | `_mm512_min_ps(a,b)` | VMINPS zmm,zmm,zmm/m512 |
| max        | `_mm512_max_ps(a,b)` | VMAXPS zmm,zmm,zmm/m512 |
| cmp_lt     | `_mm512_cmp_ps_mask(a,b,_CMP_LT_OQ)` | VCMPPS k,zmm,zmm,imm8 (imm8=0x11 for LT ordered quiet) |
| cmp_eq     | `_mm512_cmp_ps_mask(a,b,_CMP_EQ_OQ)` | VCMPPS k,zmm,zmm,imm8 (imm8=0x00) |
| and_mask   | `_mm512_kand(k1,k2)` | KANDW k,k,k |
| or_mask    | `_mm512_kor(k1,k2)` | KORW k,k,k |
| not_mask   | `_mm512_knot(k)` | KNOTW k,k |
| load       | `_mm512_load_ps(p)` | VMOVAPS zmm,[m] (aligned) |
| load_u     | `_mm512_loadu_ps(p)` | VMOVUPS zmm,[m] (unaligned) |
| store      | `_mm512_store_ps(p,v)` | VMOVAPS [m],zmm |
| gather     | `_mm512_i32gather_ps(idx,base,4)` | VGATHERDPS zmm{k},{vm32z} |
| scatter    | `_mm512_i32scatter_ps(base,idx,v,4)` | VSCATTERDPS {vm32z}{k},zmm |
| reduce_add | `_mm512_reduce_add_ps(v)` | (no single opcode; use VADDPS+shuffle tree or VREDUCE) |
| blend      | `_mm512_mask_blend_ps(k,a,b)` | VBLENDMPS zmm{k},zmm,zmm |
| broadcast  | `_mm512_set1_ps(f)` | VBROADCASTSS zmm,m32 or VPBROADCASTD |
| permute    | `_mm512_permutexvar_ps(idx,v)` | VPERMPS zmm,zmm,zmm |
| shift_l_i32| `_mm512_slli_epi32(v,imm)` | VPSLLD zmm,zmm,imm8 |
| shift_r_i32| `_mm512_srli_epi32(v,imm)` (logical) | VPSRLD zmm,zmm,imm8 |
| shr_arith_i32 | `_mm512_srai_epi32(v,imm)` | VPSRAD zmm,zmm,imm8 |
| cvt_f32_i32 | `_mm512_cvtps_epi32(v)` | VCVTPS2DQ zmm,zmm/m512 |
| cvt_i32_f32 | `_mm512_cvtepi32_ps(v)` | VCVTDQ2PS zmm,zmm/m512 |
| abs_f32    | `_mm512_abs_ps(v)` | VANDPS zmm,zmm,sign-mask (no native VABSPS) |
| neg_f32    | `_mm512_sub_ps(_mm512_setzero_ps(),v)` | VXORPS + VSUBPS |

**Note**: `_mm512_fmadd_ps(a,b,c)` computes `a*b+c`. Compiler chooses 132/213/231 form
based on which register is live. Backend authors must not assume a specific form — see
§6 errata item 6-E.

**UNVERIFIED** — verify all intrinsic names against Intel Intrinsics Guide
(intrinsics-guide.intel.com) and opcode mnemonics against Intel SDM Vol 2B.

### 5.2 ARM ACLE NEON (AArch64 Advanced SIMD)

For `float32x4_t` (4-lane f32 in a 128-bit Q register):

| Abstract Op | ACLE Intrinsic | Machine Opcode |
|---|---|---|
| add        | `vaddq_f32(a,b)` | FADD V.4S,V.4S,V.4S |
| sub        | `vsubq_f32(a,b)` | FSUB V.4S,V.4S,V.4S |
| mul        | `vmulq_f32(a,b)` | FMUL V.4S,V.4S,V.4S |
| fma        | `vfmaq_f32(c,a,b)` | FMLA Vd.4S,Vn.4S,Vm.4S (d += n*m) |
| fma_lane   | `vfmaq_laneq_f32(c,a,b,lane)` | FMLA Vd.4S,Vn.4S,Vm.S[lane] |
| sqrt       | `vsqrtq_f32(a)` | FSQRT V.4S,V.4S |
| min        | `vminq_f32(a,b)` | FMIN V.4S,V.4S,V.4S |
| max        | `vmaxq_f32(a,b)` | FMAX V.4S,V.4S,V.4S |
| min_nm     | `vminnmq_f32(a,b)` | FMINNM V.4S,V.4S,V.4S (IEEE minNum) |
| max_nm     | `vmaxnmq_f32(a,b)` | FMAXNM V.4S,V.4S,V.4S (IEEE maxNum) |
| abs        | `vabsq_f32(a)` | FABS V.4S,V.4S |
| neg        | `vnegq_f32(a)` | FNEG V.4S,V.4S |
| cmp_lt     | `vcltq_f32(a,b)` | FCMGT V.4S,V.4S,V.4S (note: reversed!) |
| cmp_eq     | `vceqq_f32(a,b)` | FCMEQ V.4S,V.4S,V.4S |
| blend      | `vbslq_f32(mask,t,f)` | BSL Vd.16B,Vn.16B,Vm.16B (bit select) |
| load       | `vld1q_f32(p)` | LD1 {V.4S},[x0] |
| store      | `vst1q_f32(p,v)` | ST1 {V.4S},[x0] |
| broadcast  | `vdupq_n_f32(f)` | DUP V.4S,Wn |
| permute/tbl| `vqtbl1q_u8(v,idx)` | TBL V.16B,{V.16B},V.16B |
| reduce_add | `vaddvq_f32(v)` | FADDP + FADDP + FADDP (or ADDV for int) |
| cvt_f32_i32| `vcvtq_s32_f32(v)` | FCVTZS V.4S,V.4S (round toward zero) |
| cvt_i32_f32| `vcvtq_f32_s32(v)` | SCVTF V.4S,V.4S |

**Note on `vcltq_f32`**: the ACLE `vclt` computes `a < b` but maps to `FCMGT b,a`
(greater-than with reversed operands). This is an important asymmetry. See §9.

**UNVERIFIED** — verify against arm_neon.h ACLE spec (ARM IHI0073 §5) and
ARMv9 ARM instruction entries.

### 5.3 ARM ACLE SVE2

For `svfloat32_t` (scalable f32 vector):

| Abstract Op | SVE2 Intrinsic (_z suffix = zeroing pred) | Pred variant | Machine Opcode |
|---|---|---|---|
| add        | `svadd_f32_z(pg,a,b)` | _m = merge, _x = undef | FADD Zd.S,Pg/M,Zn.S,Zm.S |
| sub        | `svsub_f32_z(pg,a,b)` | | FSUB Zd.S,Pg/M,Zn.S,Zm.S |
| mul        | `svmul_f32_z(pg,a,b)` | | FMUL Zd.S,Pg/M,Zn.S,Zm.S |
| fma        | `svmla_f32_m(pg,acc,a,b)` | merging only | FMLA Zda.S,Pg/M,Zn.S,Zm.S |
| sqrt       | `svsqrt_f32_z(pg,a)` | | FSQRT Zd.S,Pg/M,Zn.S |
| min        | `svmin_f32_z(pg,a,b)` | | FMIN Zd.S,Pg/M,Zn.S,Zm.S |
| max        | `svmax_f32_z(pg,a,b)` | | FMAX Zd.S,Pg/M,Zn.S,Zm.S |
| cmp_lt     | `svcmplt_f32(pg,a,b)` | returns svbool_t | FCMLT Pd.S,Pg/Z,Zn.S,Zm.S |
| cmp_eq     | `svcmpeq_f32(pg,a,b)` | | FCMEQ Pd.S,Pg/Z,Zn.S,Zm.S |
| load       | `svld1_f32(pg,base)` | | LD1W {Zd.S},Pg/Z,[Xbase] |
| store      | `svst1_f32(pg,base,v)` | | ST1W {Zn.S},Pg,[Xbase] |
| gather     | `svld1_gather_s32index_f32(pg,base,idx)` | | LD1W {Zd.S},Pg/Z,[Xbase,Zm.S,SXTW] |
| scatter    | `svst1_scatter_s32index_f32(pg,base,idx,v)` | | ST1W {Zn.S},Pg,[Xbase,Zm.S,SXTW] |
| broadcast  | `svdup_n_f32(f)` | | DUP Zd.S,#imm or MOV Zd.S,Wn |
| pred_all   | `svptrue_b32()` | | PTRUE Pd.S, ALL |
| pred_whilelt | `svwhilelt_b32(x0,x1)` | | WHILELT Pd.S,Xn,Xm |
| pred_test  | `svptest_any(pg,p)` | | PTEST Pg,Pn.B |
| count_active | `svcntp_b32(pg,p)` | | CNTP Xd,Pg,Pn.S |
| reduce_add | `svaddv_f32(pg,v)` | returns f32 scalar | FADDA Sd,Pg,Sn,Zm.S (ordered) or FADDV (unordered) |

**SVE2 predication flavors (_z, _m, _x)**:
- `_z` (zeroing): inactive lanes → 0 in dest
- `_m` (merging): inactive lanes retain dest value
- `_x` (don't care): inactive lanes undefined; allows better codegen

**UNVERIFIED** — verify against ARM ACLE SVE spec (IHI0074, §3.x) and the SVE2
instruction reference.

### 5.4 RVV Intrinsics (C API from rvv-intrinsic-doc)

For `vfloat32m1_t` (f32, LMUL=1):

| Abstract Op | RVV Intrinsic | Machine Mnemonic |
|---|---|---|
| add        | `__riscv_vfadd_vv_f32m1(a,b,vl)` | vfadd.vv vd,vs2,vs1,vm |
| sub        | `__riscv_vfsub_vv_f32m1(a,b,vl)` | vfsub.vv |
| mul        | `__riscv_vfmul_vv_f32m1(a,b,vl)` | vfmul.vv |
| fma (acc)  | `__riscv_vfmacc_vv_f32m1(acc,a,b,vl)` | vfmacc.vv vd,vs1,vs2 (vd+=vs1*vs2) |
| fma (add)  | `__riscv_vfmadd_vv_f32m1(a,b,c,vl)` | vfmadd.vv vd,vs1,vs2 (vd=vs1*vd+vs2) |
| sqrt       | `__riscv_vfsqrt_v_f32m1(a,vl)` | vfsqrt.v |
| min        | `__riscv_vfmin_vv_f32m1(a,b,vl)` | vfmin.vv |
| max        | `__riscv_vfmax_vv_f32m1(a,b,vl)` | vfmax.vv |
| cmp_lt     | `__riscv_vmflt_vv_f32m1_b32(a,b,vl)` | vmflt.vv vd,vs2,vs1,vm |
| cmp_eq     | `__riscv_vmfeq_vv_f32m1_b32(a,b,vl)` | vmfeq.vv |
| int cmp_eq | `__riscv_vmseq_vv_i32m1_b32(a,b,vl)` | vmseq.vv |
| load       | `__riscv_vle32_v_f32m1(p,vl)` | vle32.v vd,(rs1) |
| store      | `__riscv_vse32_v_f32m1(p,v,vl)` | vse32.v vs3,(rs1) |
| gather     | `__riscv_vluxei32_v_f32m1(base,idx,vl)` | vluxei32.v vd,(rs1),vs2 |
| scatter    | `__riscv_vsuxei32_v_f32m1(base,idx,v,vl)` | vsuxei32.v vs3,(rs1),vs2 |
| broadcast  | `__riscv_vfmv_v_f_f32m1(f,vl)` | vfmv.v.f vd,fs1 |
| mask_and   | `__riscv_vmand_mm_b32(a,b,vl)` | vmand.mm vd,vs2,vs1 |
| mask_or    | `__riscv_vmor_mm_b32(a,b,vl)` | vmor.mm |
| reduce_add | `__riscv_vfredosum_vs_f32m1_f32m1(acc,v,pg,vl)` | vfredosum.vs vd,vs2,vs1 |
| setvl      | `__riscv_vsetvl_e32m1(avl)` | vsetvli rd,rs1,e32,m1,ta,ma |

**Notes on RVV intrinsic naming**:
- suffix `_f32m1` = f32 element type, LMUL=1
- suffix `_b32` on mask results = 1 bit per f32 element (bit mask density)
- All intrinsics take `vl` (vector length) as the last argument; this corresponds to
  the value returned by `vsetvli`
- The `vl`-passing convention means every operation must carry the active element count

**UNVERIFIED** — verify against rvv-intrinsic-doc v1.0
(github.com/riscv-non-isa/rvv-intrinsic-doc).

### 5.5 PTX Builtins (CUDA / NVIDIA)

PTX builtins for warp-scoped operations (used via WarpVec in Wave B1 §5):

| Abstract Op | PTX Builtin / CUDA Intrinsic | PTX Instruction |
|---|---|---|
| warp_shfl_down | `__shfl_down_sync(mask,v,delta,width)` | `shfl.sync.down.b32 %d,%s,delta,width-1,mask` |
| warp_shfl_up | `__shfl_up_sync(mask,v,delta,width)` | `shfl.sync.up.b32` |
| warp_shfl_xor | `__shfl_xor_sync(mask,v,laneMask,width)` | `shfl.sync.bfly.b32` |
| warp_shfl_idx | `__shfl_sync(mask,v,srcLane,width)` | `shfl.sync.idx.b32` |
| warp_ballot | `__ballot_sync(mask,pred)` | `vote.sync.ballot.b32 %r,pred,mask` |
| warp_all | `__all_sync(mask,pred)` | `vote.sync.all.pred %p,pred,mask` |
| warp_any | `__any_sync(mask,pred)` | `vote.sync.any.pred %p,pred,mask` |
| active_mask | `__activemask()` | `activemask.b32 %r` |
| warp_reduce_add | `__reduce_add_sync(mask,v)` | `redux.sync.add.u32 %r,%s,mask` (sm_80+) |
| warp_reduce_max | `__reduce_max_sync(mask,v)` | `redux.sync.max.u32` (sm_80+) |
| tensor_mma | `wmma::mma_sync(...)` | `mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32` |
| load_matrix | `wmma::load_matrix_sync(...)` | `ldmatrix.sync.aligned.m8n8.x4.shared.b16` |

**PTX version notes**: `activemask.b32` was introduced in PTX ISA 6.2; `redux.sync`
in PTX ISA 7.0 (sm_80, Ampere architecture). For older targets, warp reduction requires
manual shfl tree.

**UNVERIFIED** — verify against NVIDIA PTX ISA Reference Manual §9.7.x
(latest, docs.nvidia.com/cuda/parallel-thread-execution/).

---

## 6. Undefined Behavior / Errata Corners

This section enumerates concrete UB and microarchitecture errata that the backend must
handle explicitly. Each item has a citation target; UNVERIFIED items must be confirmed
by C3 before encoder lock.

### 6-A. AVX-512 Unmasked Scatter with Conflicting Indices

**ISA**: AVX-512, x86-64

When `VSCATTERDPS` / `VSCATTERQPS` writes to the same memory address from multiple
vector lanes (conflicting indices), the memory write order for conflicting lanes is
architecturally undefined per Intel SDM. No exception is raised; instead, hardware
selects one of the conflicting values to commit (often the highest-index lane). Code
that relies on a specific lane winning after a scatter conflict has undefined behavior.

**Citation target**: Intel SDM Vol 2B §4.x VSCATTERDPS instruction description,
paragraph on "conflict detection" and memory ordering guarantees. **UNVERIFIED —
C3 must find the exact §4.x sub-section and confirm the UB statement.**

**Backend action**: If the compiler cannot prove scatter indices are unique, it must
either (a) insert a `VPCONFLICTD` conflict-detection check + fallback scalar loop, or
(b) conservatively use a scalar scatter. Do not silently emit AVX-512 scatter for
unverified-unique indices.

### 6-B. AVX-512 Scatter "Conflict Detection" Instruction

`VPCONFLICTD zmm{k1}, zmm/m512/m32bcst` (AVX-512CD extension, not present in all
SKX machines — requires `has_avx512cd` capability flag). If `has_avx512cd` is false,
the fallback for unique-index verification is a scalar check loop.

**Citation target**: Intel SDM Vol 2C §4.x VPCONFLICTD; Intel SDM Vol 2A §2.6.1 for
EVEX encoding of CD extension instructions. **UNVERIFIED.**

### 6-C. SVE2 Streaming Mode (SMSTART) Effect on Z/P Registers

**ISA**: ARM SVE2 / SME (Scalable Matrix Extension), ARMv9.2+

When `SMSTART SM` is executed (entering SME Streaming SVE mode), all existing Z and P
register contents are architecturally UNDEFINED. Any data live in Z0–Z31 or P0–P15
before `SMSTART` must be saved to memory. Similarly, exiting streaming mode with
`SMSTOP SM` invalidates Z/P contents.

Additionally, the vector length in streaming mode (`SVL`) may differ from the normal
SVE vector length (`VL`). Backend code must NOT assume `SVL == VL`. The backend must
generate `RDSVL` (not `RDVL`) when querying vector length inside streaming mode.

**Citation target**: ARM Architecture Reference Manual for A-profile §A1.4.2 (SME
state transitions) and §C2.1.x (streaming mode register state). Also ARM SME Programmer's
Guide §2.x. **UNVERIFIED — C3 must locate exact section.**

**Backend action**: Do not generate SVE2 vector ops within SME streaming regions
without explicit save/restore guards. Currently out-of-scope for Simple compiler targets
(no SME emission planned), but errata is documented for completeness.

### 6-D. RVV vstart != 0 Behavior on Trap-Resumed Instructions

**ISA**: RISC-V RVV 1.0

When a vector instruction is interrupted mid-execution (e.g., by a page fault in an
element, or a timer interrupt), hardware writes the faulting element index into `vstart`
and returns from the trap. On instruction resume, execution begins from element `vstart`
(skipping elements 0..vstart-1), leaving them undisturbed (RVV §3.7).

**Non-obvious consequences** (confirmed from spec §3.7):
1. Software that manually writes `vstart != 0` before a vector instruction causes the
   first `vstart` elements to be treated as prestart (undisturbed). This is a valid
   technique for partial vector initialization but must be intentional.
2. If a compiler emits `vsetvli` inside a trap handler that previously saved `vstart != 0`,
   it must preserve and restore `vstart`. Failure to do so causes the resumed instruction
   to start at element 0 instead of the interrupted element, corrupting partial results.
3. All `vset{i}vl{i}` instructions reset `vstart` to 0 on completion — so emitting a
   `vsetvli` before resuming a partially-complete vector instruction is WRONG unless
   `vstart` is explicitly re-set afterward.

**Backend action**: The Simple compiler's current strip-mining model emits `vsetvli` at
each loop iteration prolog (Wave B2 §4.6), which resets `vstart`. If the compiler ever
supports non-restartable trap contexts, it must save/restore `vstart`. For normal
user-mode loops with resumable traps, this is handled correctly by the OS on context
switch (the OS saves/restores all CSRs including `vstart`).

**Source**: RVV 1.0 §3.7 (confirmed live).

### 6-E. NEON Denormal Handling vs FPCR.FZ Bit

**ISA**: AArch64 NEON and SVE

AArch64 has a Flush-to-Zero mode controlled by `FPCR.FZ` (bit 24). When FZ=1:
- Input subnormal values are treated as +0 before the operation
- Output subnormal results are flushed to +0

NEON and SVE/SVE2 vector FP instructions honor `FPCR.FZ`. Consequences:
- Code compiled assuming IEEE-754 subnormal behavior may get incorrect results if
  running in an FZ=1 context (e.g., C libraries compiled with `-ffast-math` that set
  `FPCR.FZ=1`).
- Mixed scalar/vector code where the scalar path uses a different FPCR value than
  the vector path may produce divergent results.

Additionally, `FPCR.AH` (alternative half-precision, bit 1) affects how NEON f16
operations handle NaN encoding. Backend must not assume default FPCR state.

**Citation target**: ARMv9 ARM §A1.3.2 (FPCR register) and §G3.x (floating-point
exception trapping). **UNVERIFIED — C3 to confirm exact section numbers.**

**Backend action**: Document and test that the Simple runtime initializes FPCR to a
known value before entering vector code sections. If host FPCR is unknown, add a
`mrs/msr` guard around hot vector loops that require IEEE-754 semantics.

### 6-F. Intel VFMADD132/213/231 Form Selection: Wrong Form = Silent Reorder

**ISA**: x86 AVX-512 (also AVX, FMA3)

The three VFMADD forms (132, 213, 231) differ ONLY in which register is the
accumulator and what roles the three operands play. Selecting the wrong form does not
raise an exception; it silently computes the wrong result:

```
VFMADD132PS dst, src1, src2  → dst = (dst × src2) + src1
VFMADD213PS dst, src1, src2  → dst = (src1 × dst) + src2   ← MOST COMMON in compilers
VFMADD231PS dst, src1, src2  → dst = (src1 × src2) + dst
```

If the backend emits 132 when the semantics require 213, the multiplier and addend are
swapped, giving `(a×c)+b` instead of `(a×b)+c`. For numerically critical code this is
a silent precision regression; for code with non-commutative operands (e.g., subtraction
in the addend) it is a wrong-answer bug.

**Citation target**: Intel SDM Vol 2B §4.x VFMADD213PS instruction description.
**UNVERIFIED — C3 to verify exact form numbering convention.**

**Backend action**: The encoder must explicitly track which register holds the accumulator
and select the FMA form accordingly. Do not assume commutative FP arithmetic when
selecting VFMADD form.

### 6-G. PTX `shfl.sync` Mask Must Include Self

**ISA**: PTX / CUDA

The `mask` parameter to `shfl.sync` (and all `*.sync` warp instructions) must include
the bit for the thread executing the instruction itself. If a thread includes itself
in neither the source nor destination of a shuffle, the behavior is undefined per PTX
ISA §9.7.6.x.

Concretely: if thread lane 5 calls `__shfl_down_sync(0x0000001F, val, 2, 32)`, lane 5
is in lanes 0–4 (bits 0–4) which IS bit 5? No — mask = 0x1F = bits 0–4 = lanes 0–4.
Lane 5 is NOT in this mask. This is UB. The mask must include all participating threads.

**Citation target**: PTX ISA Reference Manual §9.7.6 (vote/shfl instructions, mask
semantics). Confirmed from Wave B2 §2.7 (PTX/WarpVec erratum). **PARTIALLY VERIFIED
via Wave B2 doc reference; confirm exact §9.7.6 text against PTX ISA PDF.**

**Backend action**: WarpVec ops must enforce `mask & (1u << lane_id) != 0` before
generating shfl.sync. The B2 §2.7 erratum documents this reconciliation.

### 6-H. Apple M-chip AMX Coprocessor vs SVE

**ISA**: Apple M-series

Apple M1/M2/M3/M4 include an "AMX" (Apple Matrix coprocessor) that is accessed via
undocumented instructions (exposed only via Accelerate framework, not as public ISA).
AMX is NOT SVE — the M-series CPUs support NEON but NOT SVE. Any code path that
detects AArch64 and emits SVE instructions will SIGILL on Apple Silicon.

The Simple compiler must gate SVE emission on the `has_sve2` capability flag, which
must be false for all Apple M-series targets. Detection: check kernel version / HWCAP
bits; on macOS, `sysctlbyname("hw.optional.arm.FEAT_SVE")` returns 0.

**Source**: Apple platform documentation (no public ISA reference for AMX). HWCAP
detection path is the only reliable check.

### 6-I. RVV: frm CSR Must Hold Valid Rounding Mode

**ISA**: RISC-V RVV 1.0

Per RVV §10.1: "Use of the `frm` field when it contains an invalid rounding mode by any
vector floating-point instruction — even those that do not depend on the rounding mode,
or when `vl=0`, or when `vstart >= vl` — is reserved."

The `frm` CSR is shared with scalar FP. If scalar FP code sets `frm` to an invalid
value (0b101, 0b110, or 0b111) and then a vector FP instruction executes, the behavior
is reserved. Some implementations raise an illegal-instruction exception; others are
silent.

**Source**: RVV §10.1 (confirmed live).

**Backend action**: Ensure `frm` is initialized to a valid rounding mode (0b000 = RNE)
before entering vector FP regions. Add CSRW frm, 0 in the vector loop prologue if the
rounding mode is not known-good.

### 6-J. RVV: Mask Register Must Be v0 for Masked Instructions

**ISA**: RISC-V RVV 1.0

The mask source for masked vector instructions is architecturally fixed to v0 (the vm
bit selects masking enabled/disabled; when enabled, the mask is ALWAYS v0). There is no
encoding to select k1–k7 style (unlike AVX-512). Consequence:

- If the compiler allocates a computed mask to v4, it must emit `vmv1r.v v0, v4` before
  the masked instruction.
- Two consecutive masked instructions with DIFFERENT mask predicates require two
  `vmv1r.v` moves to v0 between them. The register allocator must not optimize away
  this move.

**Source**: RVV §3.10 (mask register conventions), confirmed from Wave B2 §4.6.

### 6-K. NEON `vclt` / `vcgt` Operand Order Reversal

**ISA**: AArch64 NEON

ACLE `vcltq_f32(a,b)` computes `a < b` (true where a is less), but the underlying
instruction is `FCMGT Vd.4S, Vb.4S, Va.4S` (greater-than with operands swapped).
The assembler mnemonics `FCMLT` and `FCMGT` are aliases that flip operands. This is NOT
a bug — it is the specified mapping — but backend authors who write raw opcode encodings
must be aware that the register order in the machine instruction is reversed relative
to the C comparison semantics.

**Backend action**: If encoding comparison instructions at the byte level, double-check
which register field maps to which operand. Do not copy register assignments directly
from the C `vclt(a,b)` call without checking the operand order reversal.

### 6-L. AVX-512 ZMM Frequency Throttling Is Not Instruction-Level

See §7.1 for full discussion. Summary: frequency throttling from ZMM use on pre-ICL
Intel CPUs is a **microarchitectural side effect** that persists up to ~700 cycles after
the last ZMM instruction, not a per-instruction penalty. It affects ALL subsequent
instructions on the core, not just FP ops. This is not documented in the per-instruction
latency tables — it requires awareness at the backend-level scheduling stage.

---

## 7. Vector Pipeline Hazards and Scheduling

### 7.1 AVX-512 ZMM Frequency Throttling (Intel pre-Sapphire Rapids)

On Intel Skylake-X (SKX), Cascade Lake (CLX), and Ice Lake (ICL), executing 512-bit ZMM
instructions with "heavy" operations (FP arithmetic, FP compares) triggers a core
frequency reduction ("AVX-512 heavy dispatch"). This is separate from "light" AVX-512
instructions (integer moves, permutes — less throttling or none).

**Throttle mechanics** (UNVERIFIED exact values — confirm against Intel Architecture
Specification for SKX):
- On SKX: after the first heavy ZMM instruction, the core may reduce frequency by up
  to ~500–700 MHz from its all-core turbo frequency. The reduced frequency persists
  for approximately 600–700 cycles after the last ZMM instruction.
- On ICL: lighter throttling, shorter recovery. Two ZMM FMA units present.
- On SPR (Sapphire Rapids): throttling eliminated for AVX-512 — ZMM runs at full
  frequency. [UNVERIFIED for SPR elimination — verify against Intel SPR datasheet §B.x]

**Backend scheduling implication**: The Simple backend should not mix short ZMM burst
and non-ZMM code without accounting for the frequency cliff. Heuristic: if a function
uses ZMM at all, commit to ZMM for the entire hot loop nest. Do not alternate between
YMM and ZMM within the same function.

**Detection**: The `cpuid` AVX-512 feature bits do NOT indicate whether a processor
applies throttling. Runtime profiling or per-model enumeration is required.

### 7.2 SVE2 Predicate Register Dependency Hazards

SVE2 predicate operations form a dependency chain when the output predicate is consumed
by the next instruction:

```
WHILELT P0.S, X0, X1     # P0 written
FADD Z1.S, P0/M, Z1.S, Z2.S  # P0 consumed immediately — RAW hazard
```

If the execution unit for predicate production (`WHILELT`) and predicate consumption
(`FADD`) have a pipeline gap, a stall may occur. Micro-architectures with predicate
forwarding paths (Cortex-X3, Neoverse V2) handle this with 1-cycle forwarding; older
implementations may stall 2–3 cycles.

**Backend scheduling implication**: Hoist `PTRUE/WHILELT` as early as possible in the
loop prologue, before the first consumer, to allow out-of-order cores to resolve the
predicate value while arithmetic is in-flight.

### 7.3 RVV LMUL Change → Pipeline Flush on Some Implementations

`vsetvli` with a different LMUL than the previous vsetvli causes some RVV implementations
to flush the vector pipeline (all in-flight vector instructions must complete before the
new LMUL configuration takes effect). This is implementation-defined; the spec does not
require a flush, but some cores do it.

**Consequence**: Issuing `vsetvli` repeatedly inside a hot loop body (e.g., to handle
widening operations) can stall the vector pipeline each iteration.

**Backend action**: The default single-LMUL policy (Wave B2 §4.6: always LMUL=1) avoids
mid-loop LMUL changes and sidesteps this hazard. Do not introduce LMUL-changing
`vsetvli` inside inner loop bodies unless profiling shows benefit.

### 7.4 Apple M-chip FCMP / FSEL Reordering

Apple M-series (Firestorm/Avalanche µarch) is a deeply out-of-order design with a large
reorder buffer (~600 instructions on M1). NEON `FCMP` + conditional `FCSEL` sequences
are subject to speculative execution; the compiler should not assume sequential ordering.
For NEON-based min/max (using `FCMP` + `FSEL` or `FMIN`), use the direct `FMIN`/`FMAX`
instructions where available rather than compare-select chains to minimize misprediction
exposure.

### 7.5 NEON Store Buffer Coalescing

On AArch64, consecutive `ST1` instructions to sequential addresses are coalesced into
wider stores by the store buffer/line-fill buffer. This means a sequence of 4×ST1 of
4S registers writing 16 bytes each into a 64-byte cache line is effectively equivalent
to a single 64-byte cache line fill. The backend should prefer sequential stores over
strided stores for best coalescing behavior. Transposing a matrix with strided stores
pays a high coalescing penalty compared to a cache-blocked transpose.

### 7.6 RVV: vsetvli is Not Free

A common mistake is treating `vsetvli` as a zero-cost prolog. On SiFive P670 and similar
implementations, `vsetvli` is a serializing instruction with 1–2 cycle latency
(UNVERIFIED). When the element count is known at compile time and the vector type does
not change across a function, the compiler should hoist `vsetvli` above the loop rather
than re-emitting it each iteration. The strip-mining loop model in Wave B2 §4.6 does
this correctly; guard that any future optimization pass does not sink `vsetvli` into
the loop body.

---

## 8. F16 / BF16 / INT8 / Mixed-Precision

### 8.1 Intel AVX-512-FP16 (Sapphire Rapids feature flag `has_avx512fp16`)

**Feature detection**: Check CPUID leaf 7, sub-leaf 0, EDX bit 23 (AVX512_FP16).
Available on Intel Sapphire Rapids server (Xeon 4th gen) and Granite Rapids.

**Native ops** (all use ZMM registers):
- `VADDPH` — packed f16 add (16 f16 elements per ZMM)
- `VMULPH` — packed f16 multiply
- `VFMADDPH` / `VFMADD132PH/213PH/231PH` — f16 FMA (same 132/213/231 hazard as §6-F)
- `VCVTPS2PHX` — convert f32→f16 (VEX-encoded variant of existing VCVTPS2PH)
- `VCVTPH2PS` — convert f16→f32 (existed since AVX-512, accelerated in FP16 extension)
- `VFCMULCPH` / `VFMULCPH` — complex f16 multiply (for signal processing)

**Rounding**: All AVX-512-FP16 ops default to IEEE round-to-nearest-even. EVEX `{er}`
encoding enables static rounding override (same mechanism as §1.6).

**Accuracy semantics**: f16 has 10-bit mantissa, 5-bit exponent (range ~6.1e-5 to 65504).
Operations that overflow f16 produce ±inf; underflow flushes to 0 (no f16 subnormals
on some implementations — UNVERIFIED; check FPCR for AArch64; check Intel SDM for x86).

**Citation target**: Intel SDM Vol 2A §2.6.x (EVEX FP16 encoding), Intel Architecture
Instruction Set Extensions Programming Reference, Chapter 5 (FP16). **UNVERIFIED.**

### 8.2 Intel AVX-512-BF16 (`has_bf16` flag, Sapphire Rapids)

**Feature detection**: CPUID leaf 7, sub-leaf 1, EAX bit 5 (AVX512_BF16).

**Native ops**:
- `VCVTNE2PS2BF16` — convert two f32 vectors to packed bf16 (two inputs → one output,
  2 f32 elements → 2 bf16 packed into 32 bits)
- `VCVTNEPS2BF16` — single f32 vector to packed bf16
- `VDPBF16PS` — dot product of bf16 pairs accumulating to f32 (the main use case)

**BF16 format**: 1 sign bit, 8 exponent bits, 7 mantissa bits (same exponent range as
f32, truncated mantissa). Conversion f32→bf16 = truncate lower 16 bits (with optional
round-nearest). BF16 cannot represent the same range of values as f16 (fewer mantissa
bits) but has the same dynamic range as f32 (same exponent).

**VDPBF16PS semantic**:
  `result[i] = accum[i] + (a_lo[i] × b_lo[i]) + (a_hi[i] × b_hi[i])`
where lo/hi are the two bf16 pairs packed into a 32-bit element. This is the basic
AMX-like 2-way dot product accumulating in f32.

**Citation target**: Intel Architecture Instruction Set Extensions §6 (BF16). **UNVERIFIED.**

### 8.3 ARM SVE2 BF16: BFCVT / BFDOT / BFMMLA

**Feature detection** (AArch64): HWCAP2_BF16 in `/proc/cpuinfo` or
`MRRS x0, ID_AA64ZFR0_EL1` — `BF16` field. Available on Cortex-X2, Neoverse V1/V2,
Apple M-series (M2+, but only via Accelerate — not as direct SVE since M-series lacks SVE).

**Instruction reference**: ARMv9 ARM §C7.2.x per instruction entry. **UNVERIFIED
exact sub-sections.**

**Key SVE2 BF16 instructions**:
- `BFCVT Zd.H, Pg/M, Zn.S` — convert f32 (S elements in Zn) to bf16 (H elements
  in Zd). Narrows by 2×; each f32 becomes one bf16. Per-element, merging predicate.
- `BFCVTNT Zd.H, Pg/M, Zn.S` — convert f32→bf16 into the ODD half-words of Zd
  (the "narrow-to-top" interleave pattern for packing two f32 vectors side-by-side)
- `BFDOT Zda.S, Zn.H, Zm.H` — BF16 dot product accumulating to f32. Each f32 element
  of Zda accumulates the dot product of 2 bf16 pairs from Zn/Zm.
- `BFMMLA Zda.S, Zn.H, Zm.H` — 2×2 BF16 matrix multiply accumulate to f32. More
  efficient than BFDOT for matrix operations. ACLE intrinsic: `svbfmmla_f32`.
- `BFMLALB/BFMLALT` — BF16 multiply-add to f32, extracting bottom/top half-words.

**Rounding**: BF16 conversion uses round-to-nearest-even by default. No runtime rounding
mode override for BF16 conversions (unlike scalar FP CSR).

### 8.4 NEON BF16 (ARMv8.6 / ARMv9)

**Feature**: Mandatory in Armv8.6. Detection: `ID_AA64ISAR1_EL1.BF16` field.

**Key NEON BF16 instructions** (128-bit, 8 bf16 elements per Q-register):
- `BFCVT Hd, Sn` — scalar f32→bf16 conversion (not vector, despite name)
- `BFMLALB Vd.4S, Vn.8H, Vm.8H` — multiply bottom bf16 pairs, accumulate to f32x4
- `BFMLALT Vd.4S, Vn.8H, Vm.8H` — multiply top bf16 pairs, accumulate to f32x4
- `BFMMLA Vd.4S, Vn.8H, Vm.8H` — 2×2 matrix multiply-accumulate (4 f32 elements)

**ACLE intrinsics**: `vbfmlalbq_f32`, `vbfmlaltq_f32`, `vbfmmlaq_f32`.

### 8.5 RVV FP16: Zvfh Extension

**Feature**: Optional extension `Zvfh` (half-precision FP vector). Detection:
`march` string includes `zvfh`; check via `riscv_isa_string` at runtime.

**Element type**: `vfloat16m1_t` (f16, LMUL=1). SEW=16 with vsew=001.

**Key ops**: All scalar FP vector ops (vfadd, vfmul, vfmacc) apply to f16 with SEW=16.
Widening conversions: `vfwcvt.f.f.v` converts f16→f32 (doubles SEW, doubles LMUL).

**Zvfbfmin extension** (separate from Zvfh): provides BF16 load/store and narrowing
convert only — `vfncvtbf16.f.f.w` converts f32→bf16. No BF16 arithmetic natively.

**ACLE parallel**: On RISC-V, there is no native BF16 arithmetic in vector; unlike ARM
which has BFDOT, RISC-V with Zvfbfmin requires: convert bf16→f32, do f32 arithmetic,
convert back.

### 8.6 PTX BF16 + Tensor Core mma.sync

**PTX type**: `.bf16` (introduced in PTX ISA 7.0 / sm_80, Ampere).

**Operations**:
- `cvt.bf16.f32` / `cvt.f32.bf16` — scalar conversion
- For vectors: `wmma::matrix_a<16,16,16,__nv_bfloat16>` fragment type
- `mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32` — tensor-core MMA with bf16
  inputs (Ampere sm_80+)

**Rounding**: CUDA bf16 operations use round-to-nearest-even for f32→bf16 conversion
by default. The `wmma` fragment stores bf16 in paired 16-bit registers.

**INT8 tensor cores** (separate from BF16):
- `mma.sync.aligned.m16n8k32.row.col.s32.s8.s8.s32` — 8-bit integer MMA (Turing+)
- CUDA intrinsic: `wmma::mma_sync` with `nvcuda::wmma::precision::s8` fragments
- `dp4a(int,int,int)` CUDA intrinsic → `dp4a.s32.s8.s8` PTX (4-element INT8 dot, scalar)

**When to prefer f32 emulation**: If the hardware target lacks native BF16 (pre-Ampere
for PTX; pre-Sapphire-Rapids for Intel; pre-Armv8.6 for NEON), convert BF16 to f32
before arithmetic. The Simple runtime should check capability flags and emit the widened
path automatically.

**Citation target**: PTX ISA Reference Manual §9.7.x (bf16 type definition), CUDA C++
Programming Guide §7.x (tensor memory accelerator). **UNVERIFIED.**

---

## 9. Cross-ISA Op Semantic Divergences

### 9.1 `cmp_lt` Unordered Float Comparison: NaN Handling

When either operand is NaN:

| ISA | Op | NaN behavior | Standard |
|---|---|---|---|
| AVX-512 | `VCMPPS (imm8=0x01, LT_OS)` | Signals exception if SNaN; returns false for QNaN | IEEE-754 signaling |
| AVX-512 | `VCMPPS (imm8=0x11, LT_OQ)` | No exception; returns false for any NaN | IEEE-754 quiet |
| AVX-512 | `VCMPPS (imm8=0x09, LT_UQ)` | Returns true if EITHER operand is NaN (unordered) | Non-IEEE |
| NEON    | `FCMGT/FCMGE/FCMEQ` | Returns false (0) if either operand is NaN; no exception | IEEE-754 quiet |
| SVE2    | `FCMLT/FCMGT Pd/Z` | Returns false if NaN (default); no signaling | IEEE-754 quiet |
| RVV     | `vmflt.vv` | Returns false for NaN; sets fflags.NV (invalid) | IEEE-754 quiet with flag |

**Backend requirement**: The abstract `cmp_lt` op in the Simple type system (Wave B1)
must specify whether it uses the ordered-quiet (OQ) or unordered-quiet (UQ) semantics.
The default should be OQ (false for NaN). On AVX-512, use `imm8=0x11` (LT_OQ).

### 9.2 `min` / `max` NaN Handling: minNum vs minimumNumber

IEEE-754-2008 defines `minNum(a, NaN) = a` (propagates the non-NaN argument).
IEEE-754-2019 redefines `minimum(a, NaN) = NaN` (NaN always propagates).

| ISA | Op | NaN propagation semantics |
|---|---|---|
| AVX-512 VMINPS | min | Returns the non-NaN argument (IEEE-754-2008 minNum behavior) |
| NEON FMIN V.4S | min | Returns the non-NaN argument (minNum — same as AVX) |
| NEON FMINNM V.4S | min (NM) | Returns the non-NaN argument (explicitly minNum per ACLE) |
| SVE2 FMIN Zd.S | min | Returns non-NaN (minNum behavior) |
| RVV vfmin.vv | min | Returns non-NaN (IEEE-754-2008 minNum per §10.1 table) |
| Any (software) | std::min(NaN,x) | Undefined in C++; typically propagates NaN via fcmp |

**Cross-ISA divergence**: AVX `VMINPS` and NEON `FMIN` both implement the 2008 minNum
semantics (non-NaN wins). There is no current ISA that implements the 2019 `minimum`
semantics in hardware (C3 should verify this claim — it may be wrong for newer RISC-V
F extension or SVE2 updates). **UNVERIFIED.**

**Backend action**: The abstract `min`/`max` op should document its NaN contract
(minNum vs minimum). If the Simple type system requires IEEE-754-2019 minimum, the
backend must add a NaN check + blend for all ISAs currently (high overhead).

### 9.3 `shr_arith` on i32 with Shift Count == 32

Arithmetic right shift by the element bit width:

| ISA | Op | Shift count = 32 behavior |
|---|---|---|
| x86 SAR r32, cl | scalar | count is masked to 5 bits (count & 31); shift by 32 = shift by 0 (no-op) |
| AVX-512 VPSRAD zmm, imm8=32 | vector | imm8 is NOT masked; shift by 32 = implementation defined (likely shift by 0 or all-sign) |
| AVX-512 VPSRAVD zmm | variable shift | each lane shift count is modulo-masked: count & 31 |
| AArch64 ASR x,x,#32 | scalar | defined: arithmetic shift right by 32 on 64-bit reg |
| NEON SSHR V.4S, #32 | vector | shift count must be 1–32; count=32 → all sign bits |
| SVE2 ASR Zd.S, Zn.S, Zm.S | vector | UNVERIFIED: variable count; count>=32 behavior |
| RVV vssra.vv (? or vsra.vv) | vector | shift count modulo SEW per §12.x |

**Key divergence**: x86 scalar SAR masks shift count to 5 bits (shift by 32 = no-op),
while NEON SSHR with count=32 on a 32-bit element performs a full arithmetic shift
(all sign bits). Code that uses shift-by-32 to extract the sign must check per-ISA.

**Source**: Intel SDM SAR instruction §4.x (shift count masking); ARMv9 ARM SSHR
§C7.x. **UNVERIFIED for exact section numbers.**

### 9.4 Reduction Order: Left-to-Right vs Tree Reduction

| ISA | Reduction op | Order guarantee | Example |
|---|---|---|---|
| RVV | `vfredosum.vs` | Ordered: left-to-right per lane index | §14.x |
| RVV | `vfredusum.vs` | Unordered: implementation may reorder | §14.x |
| SVE2 | `FADDA Sd, Pg, Sn, Zm.S` | Sequential (ordered) | §C7.2.x |
| SVE2 | `FADDV Sd, Pg, Zn.S` | Unordered (tree/pairwise) | §C7.2.x |
| AVX-512 | (no dedicated reduction; software tree) | No order guarantee in tree | N/A |
| NEON | `FADDP` + tree | Pairwise — specific order (pairing, not left-to-right) | N/A |

**Significance**: Ordered reduction (left-to-right) is reproducible and numerically
stable; unordered reduction may produce different results depending on VL (since tree
depth changes with vector length). For the Simple `reduce_add` abstract op, document
whether ordered or unordered is semantically required.

**Sources**: RVV §14.x (vector FP reduction); ARMv9 ARM §C7.2.x FADDA vs FADDV.
**UNVERIFIED for exact sub-section numbers.**

### 9.5 Rounding Mode Override

| ISA | Mechanism | Scope |
|---|---|---|
| AVX-512 | EVEX `{er}` / `{rn-sae}` bits in P2[6:5]+P2[4]=b=1 | Per-instruction override |
| SVE2 | No per-instruction rounding override in normal mode | Uses FPCR.RMode globally |
| SVE2 streaming mode | SME FPCR context may differ | Requires SMSTART/SMSTOP save/restore |
| RVV | `vfmv.fs` sets `frm` CSR; each instruction uses `frm` | Per-CSR-write, loop-wide |
| NEON | `FPCR.RMode` field (bits 23:22) | Global; no per-instruction override |

**Key divergence**: AVX-512 allows per-instruction rounding mode override without
touching any global state. RVV requires writing the `frm` CSR (which affects ALL
subsequent FP ops). SVE2 / NEON require writing FPCR. If the Simple type system
exposes a `with_rounding_mode(Mode, expr)` construct, the backend overhead varies
dramatically: trivial on AVX-512 (EVEX bits), expensive on SVE2/NEON (FPCR save/modify/
restore), moderate on RVV (CSR write before loop, restore after).

---

## 10. Open Citations Needing Verification

The following items were not confirmed against primary specs in this research round.
Wave C3 (strict-emit) MUST verify each before locking encoder bytes or making
architectural decisions.

| ID | Claim | Required primary source |
|---|---|---|
| V-01 | EVEX P0/P1/P2 bit field layout (§1.2) — all bit positions | Intel SDM Vol 2A §2.6.1, Table 2-36 |
| V-02 | EVEX register complement encoding for ZMM16–31 (§1.3) | Intel SDM Vol 2A §2.6.1 |
| V-03 | EVEX k0 opmask is all-ones sentinel, z-bit ignored (§1.4) | Intel SDM Vol 2A §2.6.1 note on k0 |
| V-04 | EVEX broadcast factor table (§1.5) | Intel SDM Vol 2A §2.6.1, Table 2-38 |
| V-05 | EVEX rounding control encoding L'L+b (§1.6) | Intel SDM Vol 2A §2.6.1 |
| V-06 | VFMADD213PS byte sequence worked example (§1.7) | Intel SDM Vol 2B §4.x VFMADD213PS entry |
| V-07 | VFMADD 132/213/231 form semantics (§1.8, §6-F) | Intel SDM Vol 2B §4.x VFMADD213PS description |
| V-08 | SVE FADD instruction bit layout bits[31:24]=0x65 for f32 (§2.2) | ARMv9 ARM §C7.2.57 FADD |
| V-09 | SVE predicate pattern 5-bit immediate encoding (§2.3 table) | ARMv9 ARM §C1.3.2 |
| V-10 | SVE FMLA Zm field bit position in 32-bit word (§2.5) | ARMv9 ARM §C7.2.74 FMLA (vectors) |
| V-11 | PSTATE.C = "not-last active" for SVE loop control (§2.6) | ARMv9 ARM §C1.2.4 |
| V-12 | SME SMSTART invalidates Z/P registers (§6-C) | ARMv9 ARM §A1.4.2 + SME programmer guide §2.x |
| V-13 | vlmul[2:0] binary encoding 101=mf8, 110=mf4, 111=mf2 (§3.5) | RVV 1.0 spec §3.4.2 Table 4 |
| V-14 | vsetvli binary encoding top-bit disambiguator (§3.2) | RVV vcfg-format.adoc |
| V-15 | vfadd funct6=000000 OPFVV (§3.9) | RVV inst-table.adoc §10 |
| V-16 | vfmacc funct6=011000 OPFVV (§3.9) | RVV inst-table.adoc §14 |
| V-17 | All latency numbers in §4.1–4.5 (every row) | Agner Fog "Instruction Tables" latest; uops.info XML March 2026 |
| V-18 | Intel SPR no ZMM frequency throttling (§4.1 note, §7.1) | Intel SPR datasheet §B.x or Agner Fog SPR section |
| V-19 | Intel intrinsic names and opcode mapping §5.1 | Intel Intrinsics Guide (intrinsics-guide.intel.com) |
| V-20 | ARM ACLE NEON intrinsic names §5.2 | ARM ACLE spec IHI0073 §5 (arm_neon.h) |
| V-21 | ARM ACLE SVE2 intrinsic names §5.3 | ARM ACLE SVE spec IHI0074 §3.x |
| V-22 | RVV intrinsic name format `__riscv_vfadd_vv_f32m1` (§5.4) | rvv-intrinsic-doc v1.0 (github.com/riscv-non-isa/rvv-intrinsic-doc) |
| V-23 | PTX `shfl.sync` mask-must-include-self (§6-G) | PTX ISA Reference §9.7.6 |
| V-24 | AVX-512 scatter UB for conflicting indices (§6-A) | Intel SDM Vol 2B §4.x VSCATTERDPS |
| V-25 | NEON vclt→FCMGT operand reversal (§6-K, §5.2 note) | ARMv9 ARM §C7.2.x FCMGT |
| V-26 | NEON FPCR.FZ / FPCR.AH semantics (§6-E) | ARMv9 ARM §A1.3.2 |
| V-27 | AVX-512 ZMM throttle ~600-700 cycle recovery on SKX (§7.1) | Intel Architecture Spec SKX §B.x or Agner microarchitecture |
| V-28 | NEON min/max returns non-NaN (minNum) vs IEEE-754-2019 minimum (§9.2) | ARMv9 ARM §C7.2.x FMIN / IEEE-754-2019 §9.6 |
| V-29 | AVX-512 VPSRAD shift-by-32 behavior (§9.3) | Intel SDM Vol 2B §4.x VPSRAD |
| V-30 | RVV vfredosum left-to-right order guarantee (§9.4) | RVV 1.0 §14.x |
| V-31 | AVX-512-FP16 CPUID leaf 7 sub-leaf 0 EDX bit 23 (§8.1) | Intel CPUID instruction reference |
| V-32 | AVX-512-BF16 CPUID leaf 7 sub-leaf 1 EAX bit 5 (§8.2) | Intel CPUID instruction reference |
| V-33 | SVE2 BFCVT/BFDOT/BFMMLA instruction encoding (§8.3) | ARMv9 ARM §C7.2.x BFCVT / BFDOT / BFMMLA |
| V-34 | RVV Zvfbfmin has no BF16 arithmetic; convert-only (§8.5) | RISC-V Zvfbfmin extension spec |
| V-35 | PTX mma.sync bf16 variant on sm_80+ (§8.6) | PTX ISA §9.7.x; CUDA guide §7.x |
| V-36 | RVV frm must be valid for all vector FP (§6-I, §9.5) | RVV §10.1 — CONFIRMED live this round |
| V-37 | RVV mask register fixed to v0 (§6-J) | RVV §3.10 — CONFIRMED via Wave B2 §4.6 cross-ref |
| V-38 | vstart/vsetvli ordering hazard on resume (§6-D) | RVV §3.7 — CONFIRMED live this round |

---

<!-- End of document -->
<!-- Sources:
  - RISC-V V-spec v1.0: github.com/riscvarchive/riscv-v-spec (live-fetched)
  - Wave A1: doc/01_research/simd_isa_survey_2026-05-02.md
  - Wave A2: doc/01_research/simd_internal_state_2026-05-02.md
  - Wave B1: doc/04_architecture/simd_unified_architecture.md
  - Wave B2: doc/04_architecture/simd_backend_strict_emit.md
  - Agner Fog "Instruction Tables" (PDF binary; not parsed this round; cite as UNVERIFIED)
  - uops.info instructions.xml March 2026 (HTML not parsed; cite as UNVERIFIED)
  - Intel SDM Vol 2A/2B (not fetched; cite targets given for C3)
  - ARMv9 ARM (JS-rendered portal; cite targets given for C3)
-->
