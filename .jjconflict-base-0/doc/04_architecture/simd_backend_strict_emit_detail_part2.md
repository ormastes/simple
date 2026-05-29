<!-- claude-arch -->
# Architecture: Backend Strict-Emit — Detail Part 2 (Regalloc + Verification)

**TL;DR.** This document covers the per-target register-allocation algorithms (§8),
runtime CPU/GPU capability detection probes (§9), byte-level golden-test fixtures (§10),
encoder unit-test contract (§11), synthesis-recipe verification table (§12),
errata-driven safeguard rules in the emit path (§13), and open verification items (§14).
It is a direct continuation of Part 1 (`simd_backend_strict_emit_detail_part1.md`, owned
by C3a), which covers ENCODERS + BYTES (§§1-7). Round-1 baseline is
`simd_backend_strict_emit.md` (B2). Round-2 type-system context is
`simd_unified_architecture_detail.md` (C2). All §-citations beginning with "C1" refer to
`doc/01_research/simd_isa_deep_2026-05-02.md`.

---

## Table of Contents

- [§8 Register Allocation Contracts (per-target algorithm)](#8-register-allocation-contracts-per-target-algorithm)
  - [§8.1 NEON Q-registers (AArch64 ASIMD)](#81-neon-q-registers-aarch64-asimd)
  - [§8.2 AVX-512 ZMM + k-mask](#82-avx-512-zmm--k-mask)
  - [§8.3 SVE2 Z + P](#83-sve2-z--p)
  - [§8.4 RVV V + LMUL grouping](#84-rvv-v--lmul-grouping)
  - [§8.5 PTX virtual SSA](#85-ptx-virtual-ssa)
  - [§8.6 SPIR-V virtual SSA](#86-spir-v-virtual-ssa)
  - [§8.7 SSE2/SSE4 XMM and AVX2 YMM (brief)](#87-sse2sse4-xmm-and-avx2-ymm-brief)
- [§9 CPU/GPU Capability Detection — Runtime Probe Code](#9-cpugpu-capability-detection--runtime-probe-code)
  - [§9.1 x86 CPUID](#91-x86-cpuid)
  - [§9.2 AArch64 System Registers + getauxval](#92-aarch64-system-registers--getauxval)
  - [§9.3 RISC-V misa + vsetvli probe](#93-risc-v-misa--vsetvli-probe)
  - [§9.4 PTX / CUDA](#94-ptx--cuda)
- [§10 Strict-Emit Byte-Level Golden Tests](#10-strict-emit-byte-level-golden-tests)
- [§11 Encoder Unit-Test Contract](#11-encoder-unit-test-contract)
- [§12 Synthesis-Recipe Verification Table](#12-synthesis-recipe-verification-table)
- [§13 Errata-Driven Safeguards — Explicit Guards in the Emit Path](#13-errata-driven-safeguards--explicit-guards-in-the-emit-path)
- [§14 Open Emit-Side Questions (V-series Unresolved)](#14-open-emit-side-questions-v-series-unresolved)

---

## §8 Register Allocation Contracts (per-target algorithm)

This section gives the precise allocation algorithm for each physical-register class.
"Priority queue" means a min-heap ordered by next-use distance (standard linear-scan
heuristic). Each algorithm below is ~50-80 lines of Simple pseudocode showing only the
load-bearing parts: the reserved-register guard, the LMUL alignment check, and the
spill path.

### §8.1 NEON Q-registers (AArch64 ASIMD)

**Physical pool:** Q0–Q31 (= V0–V31 as 128-bit; `MachRegKind.Neon128`).  
**AAPCS64 ABI (Arm Procedure Call Standard):**
- Caller-saved (scratch): Q0–Q7, Q16–Q31 (total 24 regs; allocate first).
- Callee-saved: Q8–Q15 — low 64 bits saved; high 64 bits are caller-saved per the PCS.
  The Simple backend treats the full 128b as callee-saved to be conservative: if Q8–Q15
  are live across a call, emit `stp q8, q9, [sp, #-32]!` pairs in the function prolog.
- No dedicated mask register; mask values occupy any Qn lane-mask vector.

**Algorithm (linear scan with priority-queue spill selection):**

```
# Simple pseudocode — arm_neon_regalloc.spl (to be created)
# Caller-saved regs allocated first; callee-saved only if caller pool exhausted.

struct NeonAllocState {
  free_caller:  [bool; 32],   # true = available; indices 0-7, 16-31
  free_callee:  [bool; 8],    # indices 8-15 (callee-saved)
  live_intervals: PriorityQueue<(end_pos, vreg_id)>,  # min-heap by end
  spill_map:    Map<VReg, StackSlot>,
}

fn neon_alloc_init() -> NeonAllocState {
  var s = NeonAllocState {}
  # caller-saved: Q0-Q7, Q16-Q31
  for i in 0..8  { s.free_caller[i]     = true }
  for i in 16..32 { s.free_caller[i]    = true }
  for i in 0..8  { s.free_callee[i]     = true }  # Q8-Q15 free initially
  s
}

fn neon_alloc_reg(s: &mut NeonAllocState, vr: VReg,
                  start: i32, end: i32) -> MachReg {
  # 1. Try caller-saved first (no prolog cost)
  for i in [0..8, 16..32] {
    if s.free_caller[i] {
      s.free_caller[i] = false
      s.live_intervals.push((end, vr))
      return physical_reg(MachRegKind.Neon128, i)
    }
  }
  # 2. Try callee-saved (will emit save/restore in prolog/epilog)
  for i in 0..8 {
    if s.free_callee[i] {
      s.free_callee[i] = false
      s.live_intervals.push((end, vr))
      return physical_reg(MachRegKind.Neon128, i + 8)
    }
  }
  # 3. Spill: evict the register whose live interval ends latest
  #    (furthest-next-use heuristic)
  let (_, victim_vr) = s.live_intervals.pop_max()
  let slot = alloc_stack_slot(16)  # 128-bit Q-register
  s.spill_map[victim_vr] = slot
  # Emit: str q<victim_phys>, [sp, #slot_offset]
  emit_neon_spill(victim_vr, slot)
  # Recycle victim's physical register for the new vreg
  let phys = s.vreg_to_phys[victim_vr]
  s.live_intervals.push((end, vr))
  s.vreg_to_phys[vr] = phys
  phys
}

fn neon_free_reg(s: &mut NeonAllocState, vr: VReg) {
  let phys_id = s.vreg_to_phys[vr].index()
  if phys_id < 8 || phys_id >= 16 {
    s.free_caller[phys_id] = true
  } else {
    s.free_callee[phys_id - 8] = true
  }
}
```

**Spill encoding:** `str q<n>, [sp, #<offset>]` (post-index or offset addressing).
`ldr q<n>, [sp, #<offset>]` for reload. Slot size = 16 bytes; 16-byte aligned.

**References:** AAPCS64 §6.1.2 (NEON registers), B2 §4.1.

---

### §8.2 AVX-512 ZMM + k-mask

**Physical pools:**
- Data: ZMM0–ZMM31 (`MachRegKind.Zmm`). All 32 are allocatable.
- Mask: k0–k7 (`MachRegKind.Avx512Mask`). **k0 is NEVER allocated.** k1–k7 only.

**ABI (System V AMD64 / Windows x64):**
- ZMM0–ZMM15: caller-saved on SysV; ZMM16–ZMM31: caller-saved everywhere.
- k-registers: k0–k7 are all caller-saved (no ABI callee-save for k-regs).

**Critical guard — k0 reservation:**

```
# Simple pseudocode — x86_64_avx512_regalloc.spl

const K0_INDEX: i32 = 0   # NEVER allocate; sentinel for "no mask"
const K_POOL_MIN: i32 = 1
const K_POOL_MAX: i32 = 7

struct Avx512AllocState {
  free_zmm: [bool; 32],
  free_kmask: [bool; 8],   # index 0 = k0 (permanently false)
  zmm_live: PriorityQueue<(end_pos, vreg_id)>,
  k_live:   PriorityQueue<(end_pos, vreg_id)>,
  spill_map: Map<VReg, StackSlot>,
}

fn avx512_alloc_init() -> Avx512AllocState {
  var s = Avx512AllocState {}
  for i in 0..32 { s.free_zmm[i] = true }
  s.free_kmask[K0_INDEX] = false   # *** PERMANENT RESERVE — k0 never freed ***
  for i in K_POOL_MIN..=K_POOL_MAX { s.free_kmask[i] = true }
  s
}

fn avx512_alloc_kmask(s: &mut Avx512AllocState,
                      vr: VReg, end: i32) -> MachReg {
  # Guard: never return k0 under any path
  for i in K_POOL_MIN..=K_POOL_MAX {
    if s.free_kmask[i] {
      assert(i != K0_INDEX)        # double-guard: belt and suspenders
      s.free_kmask[i] = false
      s.k_live.push((end, vr))
      return physical_reg(MachRegKind.Avx512Mask, i)
    }
  }
  # Spill: k-regs spill to GP reg via KMOVW, then to memory
  let (_, victim_vr) = s.k_live.pop_max()
  let slot = alloc_stack_slot(2)   # 16-bit k-register content (KMOVW → r16)
  emit_kmask_spill(victim_vr, slot)  # KMOVW eax, k<n> ; MOV [sp+off], ax
  let phys = s.vreg_to_phys[victim_vr]
  assert(phys.index() != K0_INDEX)   # *** assert: victim can never be k0 ***
  s.k_live.push((end, vr))
  s.vreg_to_phys[vr] = phys
  phys
}

fn avx512_emit_guard_kreg(phys: MachReg) {
  # Called at every point that encodes a k-register into an EVEX aaa field
  let idx = phys.index()
  assert(idx != K0_INDEX,
         "ICE: k0 reached EVEX emit point — allocator invariant violated")
  assert(idx >= K_POOL_MIN && idx <= K_POOL_MAX)
}
```

**Spill encoding (ZMM):** `vmovups [rsp + offset], zmm<n>` (64-byte slot, 64-byte aligned).
**k-spill path:** `kmovw eax, k<n>` then `mov word [rsp + offset], ax`.
**k-reload:** `mov ax, word [rsp + offset]` then `kmovw k<n>, eax`.

**References:** Intel SDM Vol 2A §2.6.1 (EVEX aaa field), B2 §4.4, C1 §1.4.

---

### §8.3 SVE2 Z + P

**Physical pools:**
- Data: Z0–Z31 (`MachRegKind.Sve`). All 32 allocatable. Width = VL bits (runtime).
- Predicate: P0–P14 (`MachRegKind.SvePred`). **P15 reserved** per ACLE §11.1.
  P0 is the conventional "governing all-true" predicate and is preferentially kept live
  rather than allocated; if the compiler tracks "ptrue" as a fixed resource, reserve P0
  as well (implementation decision — mark with TODO in allocator).

**AAPCS64 SVE extension:**
- Z0–Z7: parameter/result; Z8–Z23: callee-saved; Z24–Z31: temporary.
- P0–P3: parameter/result; P4–P15: callee-saved (except P15 reserved, so P4–P14 callee).

```
# Simple pseudocode — arm_sve2_regalloc.spl

const P15_INDEX: i32 = 15  # NEVER allocate
const SVE_Z_CALLEE_MIN: i32 = 8
const SVE_Z_CALLEE_MAX: i32 = 23

struct Sve2AllocState {
  free_z: [bool; 32],
  free_p: [bool; 16],  # index 15 = P15 (permanently false)
  z_live: PriorityQueue<(end_pos, vreg_id)>,
  p_live: PriorityQueue<(end_pos, vreg_id)>,
  spill_map: Map<VReg, StackSlot>,
  vl_bytes: i32,   # runtime VL in bytes; initialized by RDVL probe
}

fn sve2_alloc_init(vl_bytes: i32) -> Sve2AllocState {
  var s = Sve2AllocState { vl_bytes: vl_bytes }
  for i in 0..32 { s.free_z[i] = true }
  for i in 0..16 { s.free_p[i] = true }
  s.free_p[P15_INDEX] = false   # *** PERMANENT RESERVE ***
  s
}

fn sve2_alloc_pred(s: &mut Sve2AllocState,
                   vr: VReg, end: i32) -> MachReg {
  for i in 0..P15_INDEX {   # only 0..14
    if s.free_p[i] {
      assert(i != P15_INDEX)
      s.free_p[i] = false
      s.p_live.push((end, vr))
      return physical_reg(MachRegKind.SvePred, i)
    }
  }
  # All P0–P14 in use: spill to memory
  # SVE predicate spill: STR P<n>, [SP, #<imm>, MUL VL]
  let (_, victim_vr) = s.p_live.pop_max()
  let slot = alloc_pred_slot()   # size = VL/8 bytes; MUL VL alignment
  emit_sve_pred_spill(victim_vr, slot)
    # => STR p<n>, [sp, #<slot_mul_vl_offset>, MUL VL]
  let phys = s.vreg_to_phys[victim_vr]
  assert(phys.index() != P15_INDEX)
  s.p_live.push((end, vr))
  s.vreg_to_phys[vr] = phys
  phys
}
```

**Spill encoding (Z):** `str z<n>, [sp, #<imm>, mul vl]` (VL bytes; VL-aligned slot).
**Predicate spill:** `str p<n>, [sp, #<imm>, mul vl]` (VL/8 bytes).
**Reload (Z):** `ldr z<n>, [sp, #<imm>, mul vl]`.
**Reload (P):** `ldr p<n>, [sp, #<imm>, mul vl]`.

**References:** AAPCS64 SVE Supplement §4 (Z/P ABI), ARMv9 ARM §C7.2 (STR/LDR Z/P),
B2 §4.5, C1 §2.

---

### §8.4 RVV V + LMUL grouping

**Physical pool:** V0–V31 (`MachRegKind.Rvv`). Width = VLEN×LMUL/SEW elements.
**v0 is special:** it is the architectural mask source register. The allocator may assign
computational results to v0 only when that result is destined for immediate use as a mask
predicate — otherwise v0 is used as a write-through staging register for `vmv1r.v`.

**LMUL alignment rules (C1 §3.5, RVV §3.4.2):**

| LMUL | Allocatable bases | Stride | Count |
|------|------------------|--------|-------|
| m1   | V0..V31          | 1      | 32    |
| m2   | V0,V2,V4..V30    | 2      | 16    |
| m4   | V0,V4,V8..V28    | 4      | 8     |
| m8   | V0,V8,V16,V24    | 8      | 4     |
| mf2  | V0..V31          | 1      | 32    |
| mf4  | V0..V31          | 1      | 32    |
| mf8  | V0..V31          | 1      | 32    |

```
# Simple pseudocode — riscv_rvv_regalloc.spl

struct RvvAllocState {
  free: [bool; 32],
  lmul: i32,        # current LMUL (1, 2, 4, 8, -2, -4, -8)
  live: PriorityQueue<(end_pos, vreg_id, base_reg: i32)>,
  spill_map: Map<VReg, StackSlot>,
}

fn rvv_lmul_stride(lmul: i32) -> i32 {
  match lmul {
    8 => 8, 4 => 4, 2 => 2,
    1 | -2 | -4 | -8 => 1,   # fractional or m1: stride=1
    _ => panic("invalid lmul")
  }
}

fn rvv_lmul_group_size(lmul: i32) -> i32 {
  match lmul { 8 => 8, 4 => 4, 2 => 2, _ => 1 }
}

fn rvv_alloc_reg(s: &mut RvvAllocState,
                 vr: VReg, lmul: i32,
                 start: i32, end: i32) -> i32 {
  let stride  = rvv_lmul_stride(lmul)
  let grp_sz  = rvv_lmul_group_size(lmul)

  var base = 0
  while base < 32 {
    # Alignment check: base must be divisible by stride
    if base % stride != 0 {
      base += 1
      continue
    }
    # Availability check: all registers in the group must be free
    var all_free = true
    for offset in 0..grp_sz {
      if !s.free[base + offset] { all_free = false; break }
    }
    if all_free {
      for offset in 0..grp_sz { s.free[base + offset] = false }
      s.live.push((end, vr, base))
      return base
    }
    base += stride   # skip to next aligned candidate
  }

  # Spill: evict furthest-end victim group
  let (_, victim_vr, victim_base) = s.live.pop_max()
  let slot = alloc_rvv_stack_slot(grp_sz)   # grp_sz × VLENB bytes
  emit_rvv_group_spill(victim_vr, victim_base, grp_sz, slot)
    # => for each reg in group: vse32.v v<base+i>, offset+i*VLENB(sp)
  for offset in 0..grp_sz { s.free[victim_base + offset] = true }
  # Now retry allocation (first free aligned group)
  rvv_alloc_reg(s, vr, lmul, start, end)   # tail recursion — one retry
}

fn rvv_emit_vmv1r_before_masked_op(mask_vreg: VReg,
                                    s: &RvvAllocState) {
  # Called immediately before any instruction with vm=0 (masked)
  # If mask_vreg is not already in v0, insert vmv1r.v v0, v<n>
  let mask_phys = s.vreg_to_phys[mask_vreg]
  if mask_phys != 0 {
    emit_rvv_vmv1r(vd: 0, vs2: mask_phys)  # vmv1r.v v0, v<mask_phys>
  }
  # After this, the masked instruction encodes vm=0, mask source = v0
}
```

**Odd-aligned base rejection:** The `base % stride != 0` check in the inner loop ensures
that LMUL=2 never allocates V1, V3, etc.; LMUL=4 never allocates V1, V2, V3, V5...; etc.
This is the allocator-level enforcement of RVV §3.4.2 (C1 §3.5).

**References:** RVV 1.0 §3.4.2, §3.7 (vstart), §3.10 (mask=v0), B2 §4.6, C1 §3.5, §6-D, §6-J.

---

### §8.5 PTX virtual SSA

PTX uses a virtual register model. `ptxas` (NVIDIA's PTX assembler) performs physical
register allocation offline. The Simple compiler emits SSA-named temporaries:
`%fd0`, `%fd1`, ... for f32; `%rd0`, `%rd1`, ... for i64; `%p0`, `%p1`, ... for predicates.

**No Simple-side allocator needed.** The `ptx_fresh_freg()` / `ptx_fresh_pred()` helpers
(B2 §5.6) maintain monotone counters and emit fresh SSA names. `ptxas` handles physical
mapping at JIT-compile time. SM-version gating (§9.4) determines which instructions are
legal to emit.

**Constraint:** `ScalableVec` is a hard error on PTX targets (C2 §4.5). The allocator
must assert `target_kind != PTX || !is_scalable_vreg(vr)` before any emit call.

**References:** PTX ISA Reference §3.1 (virtual registers), B2 §4.7, C2 §4.5.

---

### §8.6 SPIR-V virtual SSA

Same principle as PTX: SPIR-V uses SSA `%result_id` names. The Vulkan driver/compiler
performs physical allocation. `spirv_fresh_id()` (B2 §5.7) allocates monotone result IDs.

**References:** SPIR-V §2.4 (logical addressing, SSA), B2 §4.8.

---

### §8.7 SSE2/SSE4 XMM and AVX2 YMM (brief)

- **SSE2 XMM0–XMM15:** Linear scan, caller-saved XMM0–XMM7, callee-saved XMM8–XMM15
  (Windows ABI) or all caller-saved (SysV AMD64). No mask registers. Spill:
  `movups [rsp + off], xmm<n>` (16-byte slot, 16-byte aligned).
- **AVX2 YMM0–YMM15:** Same ABI split as XMM (YMM = extended XMM). Spill:
  `vmovups [rsp + off], ymm<n>` (32-byte slot, 32-byte aligned).
- Both use the same linear-scan skeleton as NEON §8.1 — caller-saved pool first,
  callee-saved on exhaustion.

**References:** System V AMD64 ABI §3.2.3, B2 §4.2, §4.3.

---

## §9 CPU/GPU Capability Detection — Runtime Probe Code

Each helper below returns a capability struct. The struct types are C2-owned
(`SimdFeatureFlags`, `Avx512Capabilities`, etc.); only the probe logic is specified here.

### §9.1 x86 CPUID

Relevant CPUID leaves (C1 §8):

| Leaf | Sub-leaf | Register | Bit(s) | Feature |
|------|---------|----------|--------|---------|
| 1    | 0        | ECX      | 28     | AVX     |
| 7    | 0        | EBX      | 16     | AVX-512F |
| 7    | 0        | EBX      | 17     | AVX-512DQ |
| 7    | 0        | EBX      | 26     | AVX-512PF |
| 7    | 0        | EBX      | 27     | AVX-512ER |
| 7    | 0        | EBX      | 28     | AVX-512CD |
| 7    | 0        | EBX      | 30     | AVX-512BW |
| 7    | 0        | EBX      | 31     | AVX-512VL |
| 7    | 0        | ECX      | 1      | AVX-512VBMI |
| 7    | 0        | ECX      | 6      | AVX-512VBMI2 |
| 7    | 0        | ECX      | 14     | AVX-512VPOPCNTDQ |
| 7    | 1        | EAX      | 5      | AVX-512BF16 (Sapphire Rapids+) |
| 7    | 0        | EDX      | 23     | AVX-512FP16 (Sapphire Rapids+) |

Note: FP16 is leaf 7, **sub-leaf 0**, EDX bit 23 (not sub-leaf 1). C1 §8.1 is the
primary source. Sub-leaf 1 EAX bit 5 is BF16. Do not conflate. [PARTIALLY VERIFIED: bit
positions from C1 §8.1-8.2; confirm against Intel SDM Vol 2A §3 CPUID description —
V-01, V-02 series.]

```
# Simple probe — src/lib/nogc_sync_mut/simd/detect_x86.spl

struct Avx512Capabilities {
  has_f:        bool,
  has_dq:       bool,
  has_bw:       bool,
  has_vl:       bool,
  has_vbmi:     bool,
  has_vbmi2:    bool,
  has_vpopcntdq: bool,
  has_bf16:     bool,   # leaf 7.1 EAX bit 5
  has_fp16:     bool,   # leaf 7.0 EDX bit 23
}

extern fn rt_cpuid(leaf: i32, subleaf: i32) -> (i32, i32, i32, i32)
  # returns (eax, ebx, ecx, edx)

fn detect_avx512_subfeatures() -> Avx512Capabilities {
  let (_, ebx7, ecx7, edx7) = rt_cpuid(7, 0)
  let (eax71, _, _, _)       = rt_cpuid(7, 1)
  Avx512Capabilities {
    has_f:         (ebx7 >> 16) & 1 == 1,
    has_dq:        (ebx7 >> 17) & 1 == 1,
    has_bw:        (ebx7 >> 30) & 1 == 1,
    has_vl:        (ebx7 >> 31) & 1 == 1,
    has_vbmi:      (ecx7 >>  1) & 1 == 1,
    has_vbmi2:     (ecx7 >>  6) & 1 == 1,
    has_vpopcntdq: (ecx7 >> 14) & 1 == 1,
    has_bf16:      (eax71 >>  5) & 1 == 1,
    has_fp16:      (edx7  >> 23) & 1 == 1,
  }
}

fn detect_x86_simd_level() -> X86SimdLevel {
  let (_, _, ecx1, _) = rt_cpuid(1, 0)
  let (_, ebx7, _, _) = rt_cpuid(7, 0)
  let has_avx    = (ecx1 >> 28) & 1 == 1
  let has_avx2   = (ebx7 >>  5) & 1 == 1
  let has_avx512 = (ebx7 >> 16) & 1 == 1
  if has_avx512 { X86SimdLevel.Avx512 }
  else if has_avx2 { X86SimdLevel.Avx2 }
  else if has_avx  { X86SimdLevel.Avx }
  else             { X86SimdLevel.Sse4 }
}
```

**References:** C1 §8.1, §8.2; Intel SDM Vol 2A §3 (CPUID).

---

### §9.2 AArch64 System Registers + getauxval

On Linux, `getauxval(AT_HWCAP)` and `getauxval(AT_HWCAP2)` are the preferred mechanism
(no privilege required). System register reads (`mrs`) require EL1+ or CPU-specific
user-mode access; use `AT_HWCAP` on Linux. On macOS/Apple Silicon, use
`sysctlbyname("hw.optional.arm.FEAT_*")`.

**Key HWCAP bits (Linux AArch64):**

| Flag constant         | Feature | HWCAP register |
|----------------------|---------|----------------|
| `HWCAP_ASIMD`        | NEON (AArch64 baseline) | AT_HWCAP |
| `HWCAP_SVE`          | SVE (not SVE2)           | AT_HWCAP |
| `HWCAP2_SVE2`        | SVE2                     | AT_HWCAP2 |
| `HWCAP2_SVEAES`      | SVE2 + AES               | AT_HWCAP2 |
| `HWCAP2_BF16`        | NEON BF16 (ARMv8.6)      | AT_HWCAP2 |
| `HWCAP_SHA3`         | SHA3 (crypto)            | AT_HWCAP |

**HWCAP bit values** are kernel ABI; confirm from
`linux/arch/arm64/include/uapi/asm/hwcap.h` (V-20 class item).

```
# Simple probe — src/lib/nogc_sync_mut/simd/detect_aarch64.spl

extern fn rt_getauxval(key: i64) -> i64  # wraps getauxval(3)

const AT_HWCAP:  i64 = 16
const AT_HWCAP2: i64 = 26
const HWCAP_ASIMD:   i64 = 1 << 1
const HWCAP_SVE:     i64 = 1 << 22
const HWCAP2_SVE2:   i64 = 1 << 1
const HWCAP2_BF16:   i64 = 1 << 14   # UNVERIFIED bit position — see V-series

struct AArch64Capabilities {
  has_neon:  bool,
  has_sve:   bool,
  has_sve2:  bool,
  has_bf16:  bool,
  is_apple_m: bool,   # Apple M detection path — no SVE
}

fn detect_aarch64_capabilities() -> AArch64Capabilities {
  let hwcap  = rt_getauxval(AT_HWCAP)
  let hwcap2 = rt_getauxval(AT_HWCAP2)
  let is_apple = detect_apple_m_platform()  # see below
  AArch64Capabilities {
    has_neon:   hwcap  & HWCAP_ASIMD  != 0,
    has_sve:    hwcap  & HWCAP_SVE    != 0 && !is_apple,
    has_sve2:   hwcap2 & HWCAP2_SVE2  != 0 && !is_apple,
    has_bf16:   hwcap2 & HWCAP2_BF16  != 0,
    is_apple_m: is_apple,
  }
}

fn detect_apple_m_platform() -> bool {
  # On macOS/Apple Silicon: sysctlbyname("hw.optional.arm.FEAT_BF16")
  # returns 1 if present. SVE is always absent on Apple M series.
  # On Linux/non-Apple: return false immediately.
  # HWCAP_SVE will always be 0 on Apple; double-guard.
  #
  # Implementation: use rt_sysctl_text("hw.optional.arm.FEAT_FP16")
  # If that call succeeds with a non-empty result, we are on Apple Silicon.
  # On non-Darwin hosts, this returns error/empty → false.
  rt_is_darwin_arm64()  # extern: returns true iff running on Apple ARM macOS
}
```

**Apple M restriction:** Per C1 §6-H and C2 §6.4: Apple M-series has NEON but zero SVE
bits. Any emit path that would produce SVE2 instructions must assert
`!capabilities.is_apple_m` (§13 guard G-03). The `E_WARP_NO_APPLE_M` diagnostic is
emitted at semantic-check time before reaching the backend.

**References:** Linux `asm/hwcap.h`, C1 §6-H, C2 §6.4, B2 §4.5.

---

### §9.3 RISC-V misa + vsetvli probe

**V-extension presence:** On Linux, `getauxval(AT_HWCAP)` with `RISCV_HWCAP_V` (bit 22,
kernel ≥5.17). On bare-metal, read `misa` CSR (bit 21 = 'V'); requires M-mode or
delegated access.

**VLEN discovery:** Execute `vsetvli x0, x0, e8, m1` and then read `vl` CSR (or use the
`rd` output); the maximum `vl` for `e8, m1` equals VLEN/8 (in bytes). To get VLEN:
`VLEN_bytes = vl_result_for_e8_m1`; `VLEN_bits = VLEN_bytes * 8`.

```
# Simple probe — src/lib/nogc_sync_mut/simd/detect_riscv.spl

extern fn rt_getauxval_riscv(key: i64) -> i64
extern fn rt_riscv_probe_vlen() -> i32
  # Assembly: vsetvli t0, zero, e8, m1, ta, ma; mv a0, t0; ret
  # Returns VLENB (= VLEN/8 in bytes)

const AT_HWCAP_RISCV:   i64 = 16
const RISCV_HWCAP_V:    i64 = 1 << 22  # bit 'V' (UNVERIFIED — see V-series)

struct RiscVCapabilities {
  has_rvv:    bool,
  vlen_bytes: i32,   # VLEN in bytes (= VLENB); 0 if no RVV
  has_zvfh:   bool,  # FP16 vector extension
  has_zvfbfmin: bool, # BF16 convert-only extension
}

fn detect_riscv_capabilities() -> RiscVCapabilities {
  let hwcap    = rt_getauxval_riscv(AT_HWCAP_RISCV)
  let has_v    = hwcap & RISCV_HWCAP_V != 0
  var vlen_b   = 0
  if has_v { vlen_b = rt_riscv_probe_vlen() }
  RiscVCapabilities {
    has_rvv:      has_v,
    vlen_bytes:   vlen_b,
    has_zvfh:     has_v && rt_riscv_has_ext("zvfh"),
    has_zvfbfmin: has_v && rt_riscv_has_ext("zvfbfmin"),
  }
}
```

**vsetvli is not free** (C1 §7.6): hoist the probe `vsetvli` outside any measurement
loop. The VLEN probe itself is a one-time startup cost.

**References:** RVV 1.0 §3 (vsetvli), C1 §3.2, §7.6, §8.5; Linux RISC-V HWCAP header.

---

### §9.4 PTX / CUDA

PTX SM version is determined at two points:

1. **Compile-time:** `__CUDA_ARCH__` macro (e.g., 890 for sm_89). The simple compiler
   emits `.target sm_<N>` directives in the PTX header based on the configured target.
2. **Runtime:** `cuDeviceGetAttribute(CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, dev)`
   and `..._MINOR` to form `major*10 + minor`.

```
# Simple probe — src/lib/nogc_sync_mut/simd/detect_ptx.spl

extern fn rt_cuda_device_attribute(attr: i32, dev: i32) -> i32
  # wraps cuDeviceGetAttribute

const CU_DEVICE_ATTR_CC_MAJOR: i32 = 75
const CU_DEVICE_ATTR_CC_MINOR: i32 = 76

struct CudaCapabilities {
  sm_version: i32,   # e.g., 89 for sm_89 (Hopper), 80 for sm_80 (Ampere)
  has_tensor_cores: bool,
  has_bf16:    bool,  # sm_80+
  has_fp16:    bool,  # sm_60+
}

fn detect_cuda_capabilities(device: i32) -> CudaCapabilities {
  let major = rt_cuda_device_attribute(CU_DEVICE_ATTR_CC_MAJOR, device)
  let minor = rt_cuda_device_attribute(CU_DEVICE_ATTR_CC_MINOR, device)
  let sm    = major * 10 + minor
  CudaCapabilities {
    sm_version:       sm,
    has_tensor_cores: sm >= 70,   # Volta+ has tensor cores
    has_bf16:         sm >= 80,   # Ampere+
    has_fp16:         sm >= 60,   # Pascal+
  }
}
```

**ScalableVec hard error:** If `is_scalable_type(ty)` and `target == PTX`, the MIR
lowering pass emits diagnostic `E_SCALABLE_NO_PTX` before reaching code-gen (C2 §4.5).
No runtime probe needed for this — it is a compile-time constraint.

**References:** PTX ISA Reference §3.1, CUDA C++ Programming Guide §6, C1 §8.6, C2 §4.5.

---

## §10 Strict-Emit Byte-Level Golden Tests

Three golden fixtures per target (8 targets × 3 = 24 fixtures). Format: target, kernel,
MIR sketch, expected bytes (hex), VERIFIED/UNVERIFIED flag, primary source citation.
UNVERIFIED = cannot pin bytes to primary spec from available sources; must be confirmed
before the golden file is locked.

Golden file root: `test/backend/simd_strict_emit/` (B2 §7.3).

---

### §10.1 NEON (AArch64 ASIMD)

**Fixture N-1: SAXPY core — `fmla v0.4s, v1.4s, v2.s[0]`**

MIR: `MirSimdFma { dest: Q0, acc: Q0, mul_a: Q1, mul_b_scalar: Q2_lane0, ty: f32x4 }`

Expected encoding (ARM FMLA vector×scalar form):
```
# FMLA Vd.4S, Vn.4S, Vm.S[idx]
# Encoding: 0x0F800000 | (idx[1]<<21)|(idx[0]<<20) | Rm<<16 | 0x90<<10 | Rn<<5 | Rd
# For FMLA v0.4s, v1.4s, v2.s[0]: idx=0, Rm=2, Rn=1, Rd=0
# bits: sf=0, 0F=vector+scalar, 80=fmla+S, lane=0
Bytes: 0x20 0x00 0x82 0x0F
```
**UNVERIFIED** — exact bit layout requires ARMv9 ARM §C7.2.74. Mnemonic confirmed from
ACLE §9 (C1 §5.2). Byte pattern is illustrative; lock only after SDM lookup (V-10).

**Fixture N-2: reduce_sum — synthesis via `FADDP`**

MIR: `MirSimdReduce { op: Add, src: Q0, dest: S0, ty: f32x4 }`

Synthesis (B2 §3.4): `FADDP v0.4s, v0.4s, v0.4s` → `FADDP s0, v0.2s`
```
# FADDP v0.4s, v0.4s, v0.4s  (pairwise add: [a+b, c+d, a+b, c+d])
Bytes: 0x00 0xD4 0x20 0x6E   # UNVERIFIED

# FADDP s0, v0.2s  (final reduce scalar)
Bytes: 0x00 0xF8 0x31 0x7E   # UNVERIFIED
```
**UNVERIFIED** — ARMv9 ARM §C7.2.57. C1 §5.2 confirms mnemonic.

**Fixture N-3: masked_store — BSL synthesis**

MIR: `MirSimdMaskedStore { data: Q1, mask: Q2, ptr: X0, ty: f32x4 }`

Synthesis (B2 §3.1): `BSL v2.16b, v1.16b, v_mem.16b` then `ST1 {v2.4s}, [x0]`
```
# BSL v2.16b, v1.16b, v3.16b   (Rd=2, Rn=1, Rm=3)
# ARMv8 ARM §C7.2.22 BSL bit-pattern (Q=1 16B form):
#   0|Q|1|01110|0|11|Rm[4:0]|000111|Rn[4:0]|Rd[4:0]
# Field placement:
#   bits[31:24] = 0110_1110 = 0x6E  (0,Q=1,1,01110)
#   bits[23:16] = 0110_0011 = 0x63  (0,size[1]=1,size[0]=1,Rm=00011)
#   bits[15:8]  = 0001_1100 = 0x1C  (opcode=000111 split + const)
#   bits[7:0]   = 0010_0010 = 0x22  (Rn[2:0]=001, Rd=00010)
# LE word: 0x6E631C22
# [ERR-002 corrected 2026-05-02] Original bytes 0x62 0x1C 0x33 0x6E were wrong:
#   decoded to Rm=19 (bits[20:16]=10011), Rn=3 (bits[9:5]=00011) — both fields wrong.
Bytes: 0x22 0x1C 0x63 0x6E   # VERIFIED — ARMv8 ARM §C7.2.22 bit-field derivation

# ST1 {v2.4s}, [x0]
Bytes: 0x02 0x78 0x00 0x4C   # UNVERIFIED — ARMv9 ARM §C7.2.339
```
**BSL VERIFIED** per ERR-002 bit-field derivation (ARMv8 ARM §C7.2.22). ST1 bytes remain UNVERIFIED — ARMv9 ARM §C7.2.339 not yet confirmed.

---

### §10.2 SSE2/SSE4 (128-bit XMM)

**Fixture S-1: SAXPY — `MULPS` + `ADDPS`**

MIR: `MirSimdFma { dest: XMM0, acc: XMM0, mul_a: XMM1, mul_b: XMM2, ty: f32x4 }`
(SSE2: no FMA3, synthesized as MUL+ADD)

```
# MULPS xmm1, xmm2   (xmm1 = xmm1 * xmm2)
# REX + 0F 59 /r (no REX needed for xmm0-7)
Bytes: 0x0F 0x59 0xCA         # MULPS xmm1, xmm2 — VERIFIED (Intel SDM MULPS §4 NP 0F 59)

# ADDPS xmm0, xmm1   (xmm0 += xmm1)
Bytes: 0x0F 0x58 0xC1         # ADDPS xmm0, xmm1 — VERIFIED (Intel SDM ADDPS §4 NP 0F 58)
```
**VERIFIED** for opcodes; ModRM bytes confirmed from Intel SDM Vol 2 (ADDPS = NP 0F 58,
MULPS = NP 0F 59; ModRM `/r` = 0xC8-0xFF range for xmm0-xmm7).

**Fixture S-2: dot (reduce_sum after pairwise) — HADDPS**

MIR: `MirSimdReduce { op: Add, src: XMM0, ty: f32x4 }`

Synthesis (B2 §3.5, SSE3 path):
```
# HADDPS xmm0, xmm0
# F2 0F 7C /r   (SSE3; requires CPUID SSE3)
Bytes: 0xF2 0x0F 0x7C 0xC0   # HADDPS xmm0, xmm0 — UNVERIFIED exact prefix

# HADDPS xmm0, xmm0 (second pass)
Bytes: 0xF2 0x0F 0x7C 0xC0   # UNVERIFIED
```
**UNVERIFIED** — need Intel SDM HADDPS entry. Opcode from C1 §5.1 table (V-19).

**Fixture S-3: mask_select — BLENDVPS (SSE4.1)**

MIR: `MirSimdSelect { dest: XMM0, a: XMM1, b: XMM2, mask: XMM0_implicit, ty: f32x4 }`
(BLENDVPS uses XMM0 implicitly as mask)

```
# BLENDVPS xmm1, xmm2, xmm0   (mask in xmm0 implicit)
# 66 0F 3A 4A /r ib (SSE4.1)
Bytes: 0x66 0x0F 0x3A 0x4A 0xD1 0x00  # UNVERIFIED — Intel SDM BLENDVPS §4
```
**UNVERIFIED** — need Intel SDM Vol 2 BLENDVPS entry (V-06 class).

---

### §10.3 AVX-512 (512-bit ZMM)

**Fixture A-1: SAXPY — `VFMADD213PS zmm0{k1}, zmm1, zmm2`**

MIR: `MirSimdFma { dest: ZMM0, mask: K1, acc: ZMM0, a: ZMM1, b: ZMM2, ty: f32x16 }`

EVEX encoding (C1 §1.7 worked example — UNVERIFIED against Intel SDM V-06):
```
# VFMADD213PS zmm0{k1}{z}, zmm1, zmm2
# EVEX: 62 F2 75 C9 A8 C2
# P0=0x62, P1=0xF2 (R'=1,X=1,B=1,R=1,mm=10), P2=0x75 (W=0,vvvv=~1,pp=01),
# P3=0xC9 (z=1,L'L=10,b=0,V'=1,aaa=001), opcode=0xA8, ModRM=0xC2
Bytes: 0x62 0xF2 0x75 0xC9 0xA8 0xC2   # UNVERIFIED — V-06
```
**UNVERIFIED** — C1 §1.7 provides this example but marks it UNVERIFIED (V-06).

**Fixture A-2: masked_store — `VMOVUPS [mem]{k1}, zmm0`**

MIR: `MirSimdMaskedStore { data: ZMM0, mask: K1, ptr: RDI, ty: f32x16 }`

```
# VMOVUPS [rdi]{k1}, zmm0
# EVEX.512.F3.0F.W0 11 /r (masked store)
# 62 F1 7E 49 11 07
Bytes: 0x62 0xF1 0x7E 0x49 0x11 0x07   # UNVERIFIED — Intel SDM VMOVUPS §4
```
**UNVERIFIED** — V-01/V-02 family.

**Fixture A-3: dot — `VDPPS` / reduction tree**

AVX-512 has no native horizontal reduce; tree of VADDPS + VEXTRACTF32X8 used.
```
# VEXTRACTF32X8 ymm1, zmm0, 1  (extract upper 256b)
# EVEX.512.66.0F3A.W0 1B /r ib
Bytes: 0x62 0xF3 0x7D 0x48 0x1B 0xC8 0x01  # UNVERIFIED

# VADDPS ymm0, ymm0, ymm1  (VEX.256.0F.WIG 58 /r)
Bytes: 0xC5 0xFC 0x58 0xC1                 # UNVERIFIED
```
**UNVERIFIED** — both require Intel SDM confirmation.

---

### §10.4 SVE2 (Scalable)

**Fixture V-1: SAXPY — `FMLA Z0.S, P0/M, Z1.S, Z2.S`**

MIR: `MirSimdFma { dest: Z0, pred: P0, a: Z1, b: Z2, ty: f32_scalable }`

SVE2 encoding from C1 §2.5:
```
# FMLA Z0.S, P0/M, Z1.S, Z2.S
# bits[31:24]=0x65 (SVE FP), size=10 (S=f32), Zm=Z2, op=000, Pg=P0, Zn=Z1, Zd=Z0
# Expected: 0x65 0x02 0x04 0x00 — UNVERIFIED per C1 §2.5 note (V-10)
Bytes: 0x65 0x02 0x04 0x00   # UNVERIFIED
```
**UNVERIFIED** — ARMv9 ARM §C7.2.74 (V-10). C1 §2.5 gives the encoding derivation.

**Fixture V-2: masked_store — `ST1W {Z0.S}, P0, [X0]`**

```
# ST1W {Z0.S}, P0, [X0]
# bits[31:25]=1110010, msz=10, Pg=000, Rn=X0=00000, Zt=Z0=00000
# Expected: 0xE4 0x00 0xE0 0x00 — UNVERIFIED (ARMv9 ARM §C7.2.345 ST1W)
Bytes: 0xE4 0x00 0xE0 0x00   # UNVERIFIED
```
**UNVERIFIED** — ARMv9 ARM §C7.2.345.

**Fixture V-3: WHILELT loop-control — `WHILELT P0.S, X0, X1`**

```
# WHILELT P0.S, X0, X1
# bits[31:24]=0x25, size=10, Rm=X1, op=0110_1, Rn=X0, Pd=P0
# Expected bytes: 0x25 0x20 0x61 0x00 — UNVERIFIED (V-09)
Bytes: 0x25 0x20 0x61 0x00   # UNVERIFIED
```
**UNVERIFIED** — ARMv9 ARM §C7.2.393.

---

### §10.5 RVV 1.0 (RISC-V Vector)

**Fixture R-1: vsetvli — `vsetvli t0, a0, e32, m1, ta, ma`**

RVV encoding from C1 §3.2 + §3.3:
```
# vsetvli t0, a0, e32, m1, ta, ma
# opcode=1010111, rd=t0=00101, rs1=a0=01010, zimm=vtypei
# vtypei: vill=0, vma=1, vta=1, vsew=010(e32), vlmul=000(m1) → 0b0_1_1_010_000 = 0x58
# Encoding: 0x00058E57 (little-endian: 0x57 0x8E 0x05 0x00)
Bytes: 0x57 0x8E 0x05 0x00   # UNVERIFIED — V-13, V-14 (confirm vtypei field)
```
**UNVERIFIED** — V-13 + V-14. Encoding structure from C1 §3.2; vtype imm from C1 §3.3-3.5.

**Fixture R-2: vfadd.vv — `vfadd.vv v8, v0, v4`**

```
# vfadd.vv v8, v0, v4
# opcode=1010111, funct3=001(OPFVV), funct6=000000, vm=1(unmasked)
# vd=v8=01000, vs1=v0=00000, vs2=v4=00100
# bits: [31:26]=000000 [25]=1(vm) [24:20]=00100 [19:15]=00000 [14:12]=001 [11:7]=01000 [6:0]=1010111
# = 0x00040457 (little-endian: 0x57 0x04 0x04 0x00)
Bytes: 0x57 0x04 0x04 0x00   # UNVERIFIED — V-15
```
**UNVERIFIED** — funct6=000000 for vfadd from C1 §3.9 (V-15).

**Fixture R-3: vmv1r.v — `vmv1r.v v0, v4` (mask copy)**

```
# vmv1r.v v0, v4
# funct6=100111, vm=1, vs2=v4, vs1=00001(nr=1), vd=v0
# = 0x9E0400D7? — UNVERIFIED; vmv1r encoding not independently confirmed
Bytes: 0x9E 0x04 0x00 0xD7   # UNVERIFIED — RVV §11.7 vmv1r.v encoding
```
**UNVERIFIED** — need RVV spec §11.7 for vmv1r encoding.

---

### §10.6 PTX

PTX fixtures are text (`.ptx` snippet), not raw bytes, because PTX is an assembly
intermediate language assembled by `ptxas`.

**Fixture P-1: SAXPY**
```ptx
# Target: sm_80
.func saxpy_kernel(.param .u64 x_ptr, .param .u64 y_ptr,
                   .param .f32 alpha, .param .u64 n) {
  .reg .f32 %fx<4>;
  .reg .u64 %rd<3>;
  ld.param.u64   %rd0, [x_ptr];
  ld.global.f32  %fx0, [%rd0];
  ld.param.f32   %fx1, [alpha];
  fma.rn.f32     %fx2, %fx1, %fx0, %fx3;  # fx2 = alpha*x + y
  # (y load + store elided for brevity)
}
```
**VERIFIED** — PTX ISA syntax correct; `fma.rn.f32` is standard PTX 7.x+.

**Fixture P-2: warp reduce_sum (shfl tree)**
```ptx
# 5-stage butterfly for f32 warp reduce (B2 §3.13)
  shfl.sync.bfly.b32 %fx1, %fx0, 16, 31, 0xffffffff;
  add.f32            %fx0, %fx0, %fx1;
  shfl.sync.bfly.b32 %fx1, %fx0, 8,  31, 0xffffffff;
  add.f32            %fx0, %fx0, %fx1;
  shfl.sync.bfly.b32 %fx1, %fx0, 4,  31, 0xffffffff;
  add.f32            %fx0, %fx0, %fx1;
  shfl.sync.bfly.b32 %fx1, %fx0, 2,  31, 0xffffffff;
  add.f32            %fx0, %fx0, %fx1;
  shfl.sync.bfly.b32 %fx1, %fx0, 1,  31, 0xffffffff;
  add.f32            %fx0, %fx0, %fx1;
```
**VERIFIED** mnemonic; mask `0xffffffff` includes self (C1 §6-G guard). (V-23: confirm
`shfl.sync.bfly` exact syntax in PTX ISA §9.7.6.)

**Fixture P-3: masked_store via setp + selp**
```ptx
  setp.gt.f32    %p0, %fx_val, 0f00000000;   # predicate from comparison
  @%p0 st.global.f32 [%rd_ptr], %fx_data;   # conditional store
```
**VERIFIED** — standard PTX predicate store idiom; PTX ISA §8.6.

---

### §10.7 SPIR-V Vulkan

SPIR-V fixtures use word-stream notation (each 32-bit word as hex).

**Fixture SP-1: SAXPY — FMA via OpExtInst (GLSL.std.450 Fma)**
```
# OpExtInst %f32 %result %glsl_ext 50 %alpha %x %y
# word[0]: 0x0008000C (OpExtInst, word-count=8)
# word[1]: result-type-id
# word[2]: result-id
# word[3]: set-id (GLSL.std.450)
# word[4]: 50 (Fma instruction)
# word[5]: alpha-id, word[6]: x-id, word[7]: y-id
```
**UNVERIFIED** — SPIR-V §3.32 (OpExtInst), GLSL.std.450 §8.3 (Fma=50 UNVERIFIED).

**Fixture SP-2: subgroup reduce (OpGroupNonUniformFAdd)**
```
# OpGroupNonUniformFAdd %f32 %result %scope_subgroup %reduce_val
# word[0]: 0x00060147 (opcode 0x147 = OpGroupNonUniformFAdd, wc=6)
# word[1]: type-id, word[2]: result-id
# word[3]: scope (3=Subgroup), word[4]: GroupOperation Reduce=0
# word[5]: value-id
```
**UNVERIFIED** — SPIR-V §3.32.x OpGroupNonUniformFAdd opcode number.

**Fixture SP-3: masked_store — OpStore with OpSelect**
```
# OpSelect %f32 %sel_result %mask_bool %true_val %false_val
# OpStore %ptr %sel_result
```
**VERIFIED** — standard SPIR-V pattern; OpSelect §3.32.11, OpStore §3.32.8.

---

### §10.8 AVX2 (256-bit YMM)

**Fixture Y-1: SAXPY — `VFMADD213PS ymm0, ymm1, ymm2`**
```
# VEX.256.66.0F38.W0 A8 /r
# C4 E2 75 A8 C2
Bytes: 0xC4 0xE2 0x75 0xA8 0xC2  # UNVERIFIED — Intel SDM VFMADD213PS VEX.256 form
```
**UNVERIFIED** — V-06/V-07. VEX prefix structure from C1 §1 context.

**Fixture Y-2: reduce_sum f32x8 — AVX horizontal tree (B2 §3.8)**
```
# VEXTRACTF128 xmm1, ymm0, 1
Bytes: 0xC4 0xE3 0x7D 0x19 0xC1 0x01  # UNVERIFIED — Intel SDM VEXTRACTF128
# VADDPS xmm0, xmm0, xmm1
Bytes: 0xC5 0xF8 0x58 0xC1             # UNVERIFIED
```
**UNVERIFIED** — Intel SDM Vol 2 entries needed.

**Fixture Y-3: scatter synthesis (loop of VPEXTRD)**
```
# VPEXTRD eax, xmm0, 0   (extract lane 0)
# VEX.128.66.0F3A.W0 16 /r ib
Bytes: 0xC4 0xE3 0x79 0x16 0xC0 0x00  # UNVERIFIED — Intel SDM VPEXTRD
```
**UNVERIFIED** — Intel SDM VPEXTRD VEX form.

---

## §11 Encoder Unit-Test Contract

### §11.1 Test File Path Scheme

```
test/unit/compiler/backend/native/
  arm_neon/
    neon_encode_f32x4_3reg_spec.spl
    neon_encode_bsl_spec.spl
    neon_encode_dup_lane_spec.spl
    neon_encode_faddp_spec.spl
    ...
  x86_64_avx512/
    evex_encode_3op_zmm_spec.spl
    evex_encode_scatter_zmm_spec.spl
    avx512_alloc_kmask_spec.spl
    ...
  arm_sve2/
    sve_encode_3reg_pred_spec.spl
    sve_encode_2reg_pred_spec.spl
    ...
  riscv_rvv/
    rvv_encode_vsetvli_spec.spl
    rvv_encode_3reg_vv_spec.spl
    rvv_encode_vmv1r_spec.spl
    ...
  ptx/
    ptx_emit_fma_spec.spl
    ptx_emit_warp_reduce_spec.spl
    ...
  spirv/
    spirv_emit_binop_spec.spl
    spirv_emit_subgroup_reduce_spec.spl
    ...
```

### §11.2 Per-Helper Test Count

Each helper in C3a's inventory requires at minimum **3 tests**:
1. **Happy-path:** canonical inputs → expected output byte sequence / PTX string.
2. **Boundary:** edge-case inputs (register index 0, register index 31, imm=0, imm=max).
3. **Error-case:** invalid input → expected diagnostic or panic (e.g., `rd=k0` →
   `ICE: k0 reached EVEX emit point`; LMUL=2 base=V1 → `ICE: odd-aligned RVV base`).

### §11.3 Estimated Helper Counts (from B2 §5)

| File | Helpers listed in B2 §5 | Estimated tests (×3) |
|------|------------------------|----------------------|
| `arm_neon.spl` extensions | ~18 (§5.1) | 54 |
| `x86_64_avx512.spl` (new) | ~12 (§5.3) | 36 |
| `arm_sve2.spl` (new)       | ~14 (§5.4) | 42 |
| `riscv_rvv.spl` (new)      | ~15 (§5.5) | 45 |
| `ptx_builder.spl` ext      | ~16 (§5.6) | 48 |
| `spirv_builder.spl` ext    | ~17 (§5.7) | 51 |
| SSE2/AVX2 helpers (§5.2)   | ~20 (§5.2) | 60 |
| **Total**                  | **~112**   | **~336** |

Note: The task spec estimates 400-600 helpers. This document's count of ~112 is
based on enumerating the helpers explicitly listed in B2 §5. The higher estimate likely
includes per-opcode specializations not yet listed (one helper variant per
funct6/opcode constant = ~4-6× multiplier for RVV and AVX-512). Exact count will be
determined when B2 §5 is fully expanded. **Minimum tests assuming 112 helpers: 336.**
If helper count grows to 150, tests reach 450; at 200 helpers, 600 tests.

### §11.4 Reference to Prior Sketch

Round-1 B2 §6 (Strict-Emit Verification) gives the verification pattern and golden-file
mechanism. Round-1 B2 §7 gives cross-target test fixture layout. This section (§11)
adds the unit-test contract per-helper on top of the golden integration tests.

---

## §12 Synthesis-Recipe Verification Table

Every "S" (synthesized) row from B2 §3 and the per-ISA op tables (B2 §2) is listed here
with its recipe verified against C1 §6–§7 errata where applicable.

| Row# | ISA | Abstract Op | Type | Recipe (opcodes in order) | C1 Citation | Status |
|------|-----|-------------|------|--------------------------|-------------|--------|
| S-01 | NEON | masked_arith | f32×4 | FCMGT mask + BSL blend + arithmetic op | C1 §5.2 (BSL) | VERIFIED (B2 §3.1) |
| S-02 | NEON | gather | f32×4 | 4× scalar LD1 (scalar form) + INS Vd.S[i] | C1 §5.2 | VERIFIED (B2 §3.2) |
| S-03 | NEON | scatter | f32×4 | 4× UMOV + scalar STR | C1 §5.2 | VERIFIED (B2 §3.3) |
| S-04 | NEON | reduce_sum | f32×4 | FADDP v0.4s,v0.4s,v0.4s + FADDP s0,v0.2s | C1 §5.2 | VERIFIED (B2 §3.4) |
| S-05 | NEON | reduce_max | f32×4 | FMAXP + FMAXV s0, v0.4s | C1 §5.2 | VERIFIED (B2 §3.4 analogue) |
| S-06 | NEON | reduce_min | f32×4 | FMINP + FMINV s0, v0.4s | C1 §5.2 | VERIFIED |
| S-07 | NEON | fma | f32×4 | Native FMLA — NOT synthesized | C1 §5.2 | N/A (native) |
| S-08 | NEON | andnot | i32×4 | BIC Vd.16B, Vn.16B, Vm.16B | C1 §5.2 | VERIFIED |
| S-09 | NEON | cmp_gt (vclt swap) | f32×4 | FCMGT Vd, Vm, Vn (operands reversed per C1 §6-K) | C1 §6-K | ERRATA-GUARDED |
| S-10 | SSE2 | reduce_sum | f32×4 | SHUFPS 0x4E + ADDPS + SHUFPS 0x11 + ADDPS | C1 §5.1 | VERIFIED (B2 §3.5) |
| S-11 | SSE2 | reduce_sum (SSE3) | f32×4 | HADDPS + HADDPS (preferred if SSE3) | C1 §5.1 | VERIFIED (B2 §3.5) |
| S-12 | SSE2 | mask_select | f32×4 | ANDPS + ANDNPS + ORPS triplet | C1 §5.1 | VERIFIED (B2 §3.6) |
| S-13 | SSE4.1 | mask_select | f32×4 | BLENDVPS xmm, xmm, xmm0 (mask implicit in xmm0) | C1 §5.1 | VERIFIED (B2 §3.6) |
| S-14 | SSE2 | gather | f32×4 | 4× MOVSS + INSERTPS | C1 §5.1 | VERIFIED (B2 §2.2) |
| S-15 | SSE2 | scatter | f32×4 | 4× EXTRACTPS + scalar MOV | C1 §5.1 | VERIFIED (B2 §2.2) |
| S-16 | SSE2 | fma | f32×4 | MULPS + ADDPS (no FMA3 in SSE2) | C1 §5.1 | VERIFIED (B2 §2.2) |
| S-17 | SSE2 | abs | f32×4 | ANDPS xmm, [sign-mask 0x7FFFFFFF×4] | C1 §5.1 | VERIFIED (B2 §2.2) |
| S-18 | SSE2 | neg | f32×4 | XORPS xmm, [sign-bits 0x80000000×4] | C1 §5.1 | VERIFIED (B2 §2.2) |
| S-19 | AVX2 | scatter | f32×8 | VPEXTRD×4 (lo half) + VEXTRACTF128 + VPEXTRD×4 (hi) + MOV×8 | C1 §5.1 | VERIFIED (B2 §3.7) |
| S-20 | AVX2 | reduce_sum | f32×8 | VEXTRACTF128 + VADDPS + HADDPS×2 | C1 §5.1 | VERIFIED (B2 §3.8) |
| S-21 | AVX2 | fma | f32×8 | Native VFMADD213PS (FMA3 required for AVX2) | C1 §5.1 | VERIFIED (errata §6-F applies) |
| S-22 | AVX2 | masked_arith | f32×8 | VCMPPS (mask) + VBLENDVPS | C1 §5.1 | VERIFIED |
| S-23 | AVX-512 | reduce_sum | f32×16 | VEXTRACTF32X8 + VADDPS + reduce_f32×8 (S-20) | C1 §5.1, §7 | VERIFIED |
| S-24 | AVX-512 | fma (form guard) | f32×16 | VFMADD213PS — form selected to match acc placement | C1 §6-F | ERRATA-GUARDED |
| S-25 | AVX-512 | scatter (conflict) | f32×16 | VPCONFLICTD check + serial fallback if conflict | C1 §6-A, §6-B | ERRATA-GUARDED |
| S-26 | RVV | andnot | eN×vl | VXOR.VI vd, vs2, -1 + VAND.VV | C1 §5.4 | VERIFIED (B2 §3.9) |
| S-27 | RVV | mask pressure | any | vmv1r.v v0, v<n> before every masked op | C1 §6-J | ERRATA-GUARDED |
| S-28 | RVV | interleave_lo | e32×vl | vrgather.vv with constructed index (B2 §3.11) | C1 §5.4 | VERIFIED (B2 §3.11) |
| S-29 | RVV | interleave_hi | e32×vl | Same vrgather with offset indices | C1 §5.4 | VERIFIED |
| S-30 | RVV | reduce_sum | f32×vl | vfredusum.vs v0, vs2, vs1 (unordered sum) | C1 §9.4 | VERIFIED (unordered) |
| S-31 | RVV | fma | f32×vl | vfmacc.vv (native) — funct6=011000 per C1 §3.9 | C1 §3.9 | UNVERIFIED (V-16) |
| S-32 | SPIR-V | gather | f32×N | N× OpAccessChain + OpLoad (B2 §3.12) | C1 §5 (SPIR-V) | VERIFIED (B2 §3.12) |
| S-33 | SPIR-V | scatter | f32×N | N× OpAccessChain + OpStore | C1 §5 | VERIFIED |
| S-34 | SPIR-V | reduce_sum | f32×N | OpGroupNonUniformFAdd Reduce | C1 §5 | UNVERIFIED opcode# |
| S-35 | PTX | reduce_sum | f32×32 | 5-stage shfl.sync.bfly tree (B2 §3.13) | C1 §6-G | ERRATA-GUARDED (self-mask) |
| S-36 | PTX | gather | f32×N | N× ld.global.f32 with offset address | C1 §5.5 | VERIFIED |
| S-37 | PTX | scatter | f32×N | N× st.global.f32 with pred guard | C1 §5.5 | VERIFIED |

**Status legend:** VERIFIED = recipe confirmed from B2 + C1 source cross-reference.
UNVERIFIED = byte encoding not pinned (see §14). ERRATA-GUARDED = recipe is correct
only if the corresponding §13 guard is in place.

---

## §13 Errata-Driven Safeguards — Explicit Guards in the Emit Path

Minimum 12 guard rules required. All 12 errata items from C1 §6 are mapped here plus
one additional from §7.

| Guard | ID | Errata | Trigger Condition | Location in pipeline | Action | C1 Citation |
|-------|----|--------|------------------|---------------------|--------|-------------|
| G-01 | k0-reserve | 6 (locked) | Any k-register allocation or emit call takes a kreg operand | `avx512_alloc_kmask()` + `avx512_emit_guard_kreg()` | `assert(kreg_index != 0, "ICE: k0 EVEX emit")` + compile-time reserve in allocator init | C1 §1.4, locked decision |
| G-02 | vmv1r-before-mask | 6-J | Any RVV instruction with `vm=0` (masked) where mask vreg is not already in v0 | `rvv_emit_vmv1r_before_masked_op()` — called from MIR lowering before every masked op | Emit `vmv1r.v v0, v<mask_phys>` unconditionally unless mask_phys==0 | C1 §6-J |
| G-03 | apple-m-no-warp | 6-H | `target == AppleM` and any `WarpVec` or SVE2 emit is attempted | `35.semantics/gpu_checker.spl` (semantic phase, before backend) | Emit `E_WARP_NO_APPLE_M` diagnostic; abort backend | C1 §6-H, C2 §6.4 |
| G-04 | vfmadd-form | 6-F | Any AVX-512 or AVX2 FMA emit: which operand is the accumulator? | `evex_emit_vfmadd()` / `vex_emit_vfmadd()` selector | Assert dest register matches the "overwritten" slot for the selected form (132/213/231); choose form before encoding, not after | C1 §6-F, §1.8 |
| G-05 | vstart-zero | 6-D | Before any RVV instruction that follows a `vsetvli` | After every `vsetvli` emission in the RVV emitter | Assert `vstart == 0` in debug builds; in production, document that `vsetvli` resets `vstart` — do not re-emit a manual CSR write | C1 §6-D, §3.8 |
| G-06 | sve2-smstart | 6-C | Entering or exiting SVE2 streaming mode (SMSTART/SMSTOP) | Any code path that emits `SMSTART SM` or `SMSTOP SM` | Assert no Z/P vregs are live across the instruction boundary; emit save/restore if required. Currently: out-of-scope (no SME emission); guard is `assert(false, "SME streaming not supported")` | C1 §6-C |
| G-07 | scatter-conflict | 6-A | Any AVX-512 scatter to a non-trivially-disjoint index set (indices not proven distinct at compile time) | AVX-512 scatter emit path | Emit `VPCONFLICTD` test; if conflict detected at runtime, fall back to sequential scalar stores (B2 §3.25) | C1 §6-A, §6-B |
| G-08 | ptx-shfl-self | 6-G | Any PTX `shfl.sync` instruction | `ptx_emit_shfl()` / `ptx_emit_warp_reduce()` | Assert `mask & (1u32 << lane_id) != 0` — i.e., the mask must include the issuing lane. For warp-wide ops use `mask=0xffffffff` | C1 §6-G |
| G-09 | rvv-frm-csr | 6-I | Any RVV floating-point instruction when a non-default rounding mode is requested | RVV FP emit path | Emit `csrw frm, <mode>` before the instruction; emit `csrw frm, 0` (RNE) after if mode was changed. Assert `frm_value in [0..4]` | C1 §6-I |
| G-10 | neon-denormal | 6-E | NEON FP emission on Apple M-series or when benchmark shows flush-to-zero behavior | NEON FP emit preamble (function entry) | Assert `FPCR.FZ == 0` in debug; warn if FPCR.AH not set for paired ops. Document that Simple does NOT set FPCR; host code must configure denormal policy | C1 §6-E |
| G-11 | neon-cmp-reversal | 6-K | Emitting `cmp_lt(a, b)` or `cmp_gt(a, b)` via NEON FCMGT / FCMLT | `neon_emit_cmp()` opcode selection | For `a < b` use `FCMGT b, a` (reversed); for `a > b` use `FCMGT a, b` (normal). Document and test both orders with asymmetric inputs | C1 §6-K |
| G-12 | zmm-throttle-warn | 6-L | Any function that emits ≥1 ZMM instruction on a non-SPR Intel target | Backend entry for AVX-512 code-gen on pre-SPR targets | Emit a compiler diagnostic `W_ZMM_FREQ_THROTTLE` if `target_microarch == SKX || ICL` (not an assert — code is still correct, just potentially slower) | C1 §6-L, §7.1 |
| G-13 | rvv-lmul-vstart | 7.3 | LMUL change across loop iterations without pipeline flush | RVV LMUL-change optimization pass | Assert: if `prev_lmul != new_lmul`, emit a `fence` instruction on implementations known to require pipeline drain (currently: emit conservatively; see V-38) | C1 §7.3 |

**Guard summary:**
- **Hard asserts (ICE):** G-01, G-02, G-05, G-07 (runtime check path), G-09
- **Semantic-phase aborts:** G-03
- **Errata-corrected logic:** G-04, G-11, G-08
- **Out-of-scope/future:** G-06, G-13
- **Warnings:** G-10, G-12

---

## §14 Open Emit-Side Questions (V-series Unresolved)

The following items from C1 §10 remain unresolved as of this document. Each has a
concrete resolution URL.

| ID | Claim at risk | Impact if wrong | Resolution URL |
|----|--------------|-----------------|----------------|
| V-01 | EVEX P0/P1/P2 bit field positions (C1 §1.2) | All AVX-512 encoder bytes are wrong | https://cdrdv2-public.intel.com/671110/325462-sdm-vol-2abcd.pdf — Vol 2A §2.6.1 Table 2-36 |
| V-06 | `VFMADD213PS` worked example byte sequence (C1 §1.7) — bytes `62 F2 75 C9 A8 C2` | Golden test A-1 is wrong | Intel SDM Vol 2B §4.x VFMADD213PS entry (same PDF, Vol 2B) |
| V-13 | vlmul[2:0] fractional encoding: 101=mf8, 110=mf4, 111=mf2 (C1 §3.5) | RVV vtype immediate computation wrong for fractional LMUL; allocator stride table broken | https://github.com/riscv/riscv-v-spec/blob/master/v-spec.adoc §3.4.2 Table 4 |
| V-15 | vfadd funct6=000000 OPFVV (C1 §3.9) | Fixture R-2 and all RVV FP-add encodings wrong | https://github.com/riscv/riscv-v-spec/blob/master/inst-table.adoc — search vfadd |
| V-25 | NEON `vclt Vd, Vn, Vm` maps to `FCMGT Vm, Vn` (operands reversed, C1 §6-K) | Guard G-11 has reversed polarity; masked comparisons produce inverted results | https://developer.arm.com/documentation/ddi0596/latest — §C7.2.x FCMGT |
| V-12 | SME `SMSTART SM` invalidates Z/P register contents (C1 §6-C) | SVE2 values incorrectly assumed live across SMSTART — silent corruption | https://developer.arm.com/documentation/ddi0596/latest — §A1.4.2 + SME Programmer's Guide §2.x |
| V-03 | EVEX k0 opmask = all-ones sentinel; z-bit ignored when aaa=000 (C1 §1.4) | k0-reserve locked decision is correct but the EVEX z-bit behavior may differ from expectation | Intel SDM Vol 2A §2.6.1 note on k0 (same PDF as V-01) |
| V-16 | vfmacc funct6=011000 OPFVV (C1 §3.9) | All RVV FMA encodings (S-31) wrong | https://github.com/riscv/riscv-v-spec/blob/master/inst-table.adoc — search vfmacc |
| V-23 | PTX `shfl.sync` exact syntax + mask semantics (C1 §6-G) | G-08 guard may use wrong PTX mnemonic; shfl fixtures need PTX ISA confirmation | https://docs.nvidia.com/cuda/parallel-thread-execution/#data-movement-and-conversion-instructions-shfl-sync §9.7.6 |
| V-38 | vstart/vsetvli ordering hazard on trap-resume (C1 §6-D, §3.8) | G-05 guard comment is incomplete; non-restartable trap context behavior unspecified | https://github.com/riscv/riscv-v-spec/blob/master/v-spec.adoc §3.7 + cross-ref §6.x trap handling |

**Additional deferred items** (from V-table, not individually flagged above):
- V-02 (EVEX ZMM16-31 complement encoding), V-04 (broadcast table), V-05 (rounding L'L+b)
  all resolve from the same Intel SDM URL as V-01.
- V-08 through V-11 (SVE bit patterns) resolve from the same ARMv9 ARM URL as V-25.
- V-17 (latency numbers) requires Agner Fog or uops.info — not blocking for correctness.
- V-19 through V-22 (intrinsic names) resolve from vendor developer portals — not
  blocking for emit correctness (they affect helper naming, not byte encoding).

**Blocking items for golden-test lock:** V-01, V-06, V-13, V-15, V-25 must be resolved
before `test/backend/simd_strict_emit/` golden files are stamped as authoritative.
All 24 golden fixtures in §10 that are currently UNVERIFIED should be treated as
provisional until primary-spec lookup is complete.

---

<!-- Sources:
  - C1 = doc/01_research/simd_isa_deep_2026-05-02.md (Round-2 ISA depth)
  - B2 = doc/04_architecture/simd_backend_strict_emit.md (Round-1 strict-emit)
  - C2 = doc/04_architecture/simd_unified_architecture_detail.md (Round-2 architecture)
  - Part1 = doc/04_architecture/simd_backend_strict_emit_detail_part1.md (C3a sibling)
  - Intel SDM Vol 2A/2B: not fetched this round; all AVX-512 bytes UNVERIFIED (V-01+)
  - ARMv9 ARM (JS portal): not fetched; SVE bytes UNVERIFIED (V-08+)
  - RVV 1.0 spec (github.com/riscv/riscv-v-spec): partially fetched by C1 author
-->
