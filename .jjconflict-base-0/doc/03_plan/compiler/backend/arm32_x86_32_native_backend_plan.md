# arm32 and x86_32 Native Codegen Backend — Implementation Plan

## 1. Current State

### 1.1 Native backend inventory (`src/compiler/70.backend/backend/native/`)

Backends are flat files, not subdirectories: `isel_<arch>.spl` (MIR → MachInst
selection) + `encode_<arch>.spl` (MachInst → bytes), dispatched from a single
`mod.spl`.

| Arch    | isel file | LOC | encode file | LOC | extra SIMD encode files |
|---------|-----------|-----|-------------|-----|--------------------------|
| riscv32 | isel_riscv32.spl | 573 | encode_riscv32.spl | 460 | encode_rvv_{int,float,fixedpt,mask,misc,permute,widen,zvk}.spl (8 files) |
| riscv64 | isel_riscv64.spl | — | encode_riscv64.spl | — | shares rvv_* files with riscv32 |
| aarch64 | isel_aarch64.spl | 686 | encode_aarch64.spl | 516 | encode_aarch64_{crypto,neon_cmp,neon_int,sve2_cmp,sve2_pred}.spl (5 files) |
| x86_64  | isel_x86_64.spl | 606 | encode_x86_64.spl | 589 | encode_x86_64_{avx2_cmp,avx2_fp,avx2_int,bmi2,crypto,fma3,sse41}.spl (7 files) |
| **arm32** | — | 0 | — | 0 | none |
| **x86_32** | — | 0 | — | 0 | none |

Baseline scalar isel+encode pair costs **~1000–1200 LOC**; each ISA extension
family adds another **~150–400 LOC** per file. riscv32/x86_64/aarch64 all
required 5–8 extra SIMD/crypto files beyond the scalar baseline.

### 1.2 Shared framework (arch-agnostic, reused by all 4 existing backends)

- `regalloc.spl` (534 LOC) — register allocator, no arch-specific branching found beyond register class inputs.
- `mach_inst.spl` (676 LOC) — shared `MachInst` instruction representation used by all `isel_*` modules.
- `encode_common.spl` (14 LOC) — thin shared encode helpers.
- `mod.spl` (345 LOC) — top-level `compile_native(module, target)` dispatch:
  ```
  match target:
      X86_64: compile_native_x86_64(module)   # isel_module -> regalloc -> encode_module -> emit_elf_x86_64
      Aarch64: compile_native_aarch64(module)
      Riscv64: compile_native_riscv64(module)
      Riscv32: compile_native_riscv32(module)  # -> emit_elf32_riscv32 (custom ELF32 path, ~30 lines)
      MachoAarch64 / MachoX86_64: ...
  ```
  **There is no `Arm32` or `X86` (x86_32) arm in this match at all** — this is
  the single chokepoint that must be extended.
- **Calling convention layer is already arch-ready, contrary to the task's framing.**
  `calling_convention.spl` (331 LOC) already implements:
  - `get_x86_abi(conv)` (line 150) — x86_32 **cdecl** (all-stack args) and
    **stdcall** (callee-cleans) are both implemented.
  - `get_arm_abi(conv)` (line 221) — ARM EABI/AAPCS32 is implemented.
  - `get_x86_64_abi`, `get_aarch64_abi` (AAPCS64), `get_riscv32_abi`,
    `get_riscv64_abi` also present, plus legacy 8-bit MCU ABIs (avr, 8051,
    msp430, i8086).
  This means **no new ABI-modeling work is needed for baseline x86_32/arm32
  codegen** — `AbiInfo` records already exist; only the isel/encode layers
  need to call into them (mirroring how `isel_riscv32.spl` calls
  `get_riscv32_abi`).
  `callconv_bridge.spl` (85 LOC) is a small mapper from `@callconv("X")`
  source attributes to the `CallingConvention` enum — also arch-agnostic,
  no changes needed.
  `arch_rules.spl` (219 LOC) is **not** part of the codegen ABI story — it is
  an unrelated dependency-boundary/import-rule linter (`ArchRule`,
  `ArchViolation`, parses `.sdn` rule files). Do not conflate it with calling
  convention when scoping this work.

### 1.3 arm32 assets that already exist (compiler side)

- `src/compiler/70.backend/lowering/intrinsic_lowering_arm32.spl` (200 LOC) —
  **lowering-decision-only**, no encoder. Defines `ArmCaps`-driven predicates
  (`arm32_can_lower_natively`, `arm32_needs_software_fallback`,
  `arm32_permanently_unavailable`) documenting real ISA gaps vs AArch64:
  no 64-bit GPRs, fixed-128-bit NEON only (no SVE2), no SHA-512/CRC32-64/
  64-bit CLMUL, CLZ from ARMv5, RBIT from ARMv6T2.
- `feature_caps_arch32.spl` (674 LOC) — `ArmCaps` (Thumb2/Cortex-M/Cortex-A32),
  `Rv32Caps`, `X86_32Caps` capability structs + `TargetCapsKind` dispatch enum
  + family-matrix rows. This is the intrinsic/idiom-availability layer, separate
  from and upstream of isel/encode.
- `baremetal/arm/{crt0.s, linker.ld}` + `baremetal/cortex_m33/*.ld` — startup/
  link assets exist for some 32-bit ARM baremetal targets, unconnected to any
  encoder today.
- `os/kernel/arch/arch_context.spl` already defines `Architecture.Arm32`,
  `Arm32Context`, `JmpBufArm32` — kernel-side register-state *shape* is
  defined and awaiting a real HAL implementation.
- No arm32 QEMU/system test exists anywhere in `test/03_system/os/qemu/`.

### 1.4 x86_32 assets that already exist (much larger footprint than arm32)

- **A full kernel arch tree already exists** and compiles against no native
  x86_32 backend yet:
  `src/os/kernel/arch/x86_32/{boot,console,context,cpu,cstart,early_syscall,
  entropy,interrupt,mod,paging,timer,trap_model,trap_runtime,user_entry}.spl`
  + `src/os/kernel/arch_adapt/x86_32/{boot,console,context,cpu,interrupt,mod,
  paging,timer}.spl` — **2285 LOC combined**.
- `feature_caps_arch32.spl` → `X86_32Caps`.
- `arch_context.spl` → `Architecture.X86`, `X86Context`, `JmpBufX86`.
- `src/os/kernel/arch/hal.spl` line 7 states explicitly: *"arm64, arm32,
  riscv64, riscv32, x86_32: imports stripped to x86_64-only... Import-closure
  bugs in the native SimpleOS kernel build mean this module cannot safely
  import every arch's concrete HAL implementation."* — i.e. the x86_32 kernel
  code exists but is **currently disconnected from the build on purpose**,
  independent of the missing codegen backend.
- **Concrete, currently-red consumer**: `test/03_system/os/qemu/
  sys_qemu_x86_32_fs_exec_spec.spl` boots `qemu-system-x86_64` in 32-bit PVH
  mode against `build/os/simpleos_x86_32_initrd_fs_exec_probe.elf` +
  `build/os/fat32-x86_32.img`, and explicitly documents "A missing kernel is
  a diagnosed RED failure. Never uses skip()." This test **cannot pass until
  an x86_32 native backend exists** to produce that ELF — it is the strongest
  demand signal for this whole plan.
- No x86_32 entries exist in `target_presets.spl` (current presets: cortex-m4/
  m33/m0, riscv32-baremetal, riscv64-linux, wasm32, linux-x86_64, macos-arm64,
  windows-x86_64) and no `baremetal/x86_32/{crt0.s,linker.ld}`.

## 2. Gap Analysis

1. **No `isel_arm32.spl`/`encode_arm32.spl`, no `isel_x86_32.spl`/`encode_x86_32.spl`** — the actual missing deliverable.
2. **`mod.spl`'s `compile_native` match has no `Arm32`/`X86` arm** — even with encoders written, nothing routes to them.
3. **`target_presets.spl` has no arm32 or x86_32 preset** — no way to select these targets via `-target` today.
4. **No `baremetal/x86_32/{crt0.s,linker.ld}`** — needed once x86_32 baremetal/kernel binaries can be produced.
5. **`hal.spl` deliberately strips x86_32/arm32 imports** due to an unresolved import-closure bug — this is a *build-hygiene* blocker independent of codegen, but it gates Phase 3 (kernel integration) even after the backend exists.
6. **No arm32 system/QEMU test exists** — unlike x86_32, there is no pre-built failing acceptance gate; one should be authored alongside the backend or the work risks going stale immediately (as x86_32's kernel tree did before its QEMU test was written).

## 3. Reuse Strategy

### x86_32 — high reuse from `encode_x86_64.spl`/`isel_x86_64.spl`
x86_32 (IA-32) and x86_64 share the same mnemonic space and ModRM/SIB
encoding scheme for the common integer/float subset; x86_32 is strictly
simpler:
- No REX prefix, no r8–r15, no 64-bit operand-size override — remove that
  logic wholesale rather than gate it.
- No RIP-relative addressing (absolute/disp32 addressing only).
- `get_x86_abi()` (cdecl/stdcall, all-stack args for cdecl) already exists in
  `calling_convention.spl` — reuse directly, unlike x86_64's register-arg ABI.
- GOT/PLT: `got_plt_builder.spl` should be checked for 64-bit-only assumptions
  before reuse in Phase 2 PIC support.
- **Estimate**: expect to strip/rewrite ~50–60% of `encode_x86_64.spl`'s
  opcode tables (drop REX-dependent forms, narrow the GPR table from 16 to 8
  legacy regs) rather than write from scratch. `isel_x86_64.spl` reuse is
  lower (~30–40%) since MIR-to-MachInst pattern selection still needs
  32-bit-specific address/immediate handling.

### arm32 — lower reuse than x86_32; closer to a fresh backend at riscv32 scale
ARM32 (A32/Thumb2) is *not* a truncated AArch64: AArch64's A64 is a fixed-32-
bit uniform encoding with no per-instruction condition codes, while A32 has a
4-bit condition field on nearly every instruction and Thumb2 mixes 16-bit and
32-bit instruction widths. `encode_aarch64.spl` cannot be mechanically
narrowed the way `encode_x86_64.spl` can — expect a build closer in effort to
`isel_riscv32.spl`/`encode_riscv32.spl` (1033 LOC combined) than to a diff of
the AArch64 files. What **does** reuse directly:
- `get_arm_abi()` (AAPCS32) already implemented in `calling_convention.spl`.
- `ArmCaps` idiom-availability predicates in `intrinsic_lowering_arm32.spl`
  and `feature_caps_arch32.spl` already document exactly which SIMD/crypto
  idioms are permanently unavailable on ARM32 (see §1.3) — the encoder's
  "must not attempt to encode this" list is already written.
- `mach_inst.spl`/`regalloc.spl` — arch-agnostic, reuse as-is (see risk in §7 re: register pressure).

## 4. Phased Implementation Plan

### Phase 1 — Minimal hosted scalar backend (unblocks the x86_32 QEMU test and basic arm32 codegen)
- `backend/native/isel_x86_32.spl` + `encode_x86_32.spl`: scalar
  integer/float ISA, cdecl only, ModRM/SIB addressing without REX.
- `backend/native/isel_arm32.spl` + `encode_arm32.spl`: A32 (not Thumb2 yet)
  scalar integer ISA, AAPCS32 only.
- Extend `mod.spl`'s `compile_native` match with `X86` → `compile_native_x86_32`
  and `Arm32` → `compile_native_arm32`, each following the existing
  `isel_module → regalloc → encode_module → emit_elf` shape. x86_32 needs an
  ELF32 writer — riscv32's `emit_elf32_riscv32` (mod.spl:103–133) is the only
  existing ELF32 path and is hand-rolled/ad hoc (~30 lines); verify it
  generalizes or budget a small shared `emit_elf32` helper.
- `target_presets.spl`: add `preset_linux_x86_32()` / `preset_x86_32_baremetal()`
  and an arm32 preset (e.g. `cortex-a32` or generic `armv7a-baremetal`),
  following the existing preset struct/`preset_by_name` pattern.
- **Effort**: ~1000–1200 LOC per backend (isel+encode), ~100–150 LOC of
  `mod.spl`/`target_presets.spl` wiring. Total Phase 1: roughly the size of
  the existing riscv32 backend, twice over.

### Phase 2 — Full ISA + calling-convention coverage
- x86_32: SSE2/SSE4.1 subset (mirror `encode_x86_64_sse41.spl` minus 64-bit
  forms), fastcall/vectorcall variants already enumerated in
  `CallingConvention` but need `AbiInfo` bodies if not already covered by
  `get_x86_abi`, PIC via GOT (reuse `got_plt_builder.spl` after auditing for
  64-bit assumptions).
- arm32: NEON32 (fixed 128-bit, mirror a trimmed `encode_aarch64_neon_int/cmp.spl`),
  Thumb2 encoding mode (16/32-bit mixed width — largest single chunk of new
  work in this whole plan), VFP scalar float if not covered by Phase 1.
- **Effort**: ~600–1000 LOC per backend, mirroring the 5–8 extra SIMD files
  seen in existing backends.

### Phase 3 — Baremetal + kernel integration
- Add `baremetal/x86_32/{crt0.s, linker.ld}` (mirror `baremetal/x86_64` and
  `baremetal/riscv`).
- Investigate and fix the `hal.spl` import-closure bug (§1.4) — do not simply
  revert the stripped imports; the comment implies a real build-graph issue.
  This is a prerequisite for linking the existing 2285 LOC of x86_32 kernel
  code into a full binary.
- Wire `src/os/kernel/arch/x86_32` + `arch_adapt/x86_32` through the new
  x86_32 backend end-to-end; make
  `test/03_system/os/qemu/sys_qemu_x86_32_fs_exec_spec.spl` pass — this is
  the concrete, already-written acceptance gate for x86_32.
  For arm32, no equivalent kernel consumer/system test exists yet; either
  scope arm32 to "compiler-completeness" (cross-compile target only, no
  kernel integration) or author a new QEMU arm32 system test in this phase
  to avoid the backend going stale immediately.
- **Effort**: variable — dominated by the hal.spl import-closure investigation, not new LOC.

## 5. Effort Estimate Summary

| Phase | x86_32 | arm32 | Basis |
|-------|--------|-------|-------|
| 1 (scalar isel+encode+wiring) | ~1100–1300 LOC | ~1000–1200 LOC | riscv32 (1033 LOC) / x86_64 (1195 LOC) baselines |
| 2 (SIMD/ISA extensions) | ~600–900 LOC | ~700–1000 LOC (Thumb2 heaviest) | aarch64/x86_64 extra-file counts (5–8 files, 150–400 LOC each) |
| 3 (baremetal/kernel) | small LOC, large investigation cost (hal.spl bug) | small LOC unless new QEMU test authored | existing 2285 LOC kernel tree + hal.spl comment |
| Tests (Phase 1) | mirror `isel_riscv32_spec.spl` (765) + `encode_riscv32_spec.spl` (101) | same pattern | existing spec LOC |

## 6. Test Strategy

- Mirror existing patterns exactly: `test/01_unit/compiler/backend/native/isel_riscv32_spec.spl` (765 LOC, the largest and most thorough of the existing isel specs) and `encode_riscv32_spec.spl` (101 LOC) are the template to copy for `isel_x86_32_spec.spl`/`encode_x86_32_spec.spl` and `isel_arm32_spec.spl`/`encode_arm32_spec.spl`.
- `isel_x86_64_spec.spl` (173 LOC) / `encode_x86_64_spec.spl` (12 LOC) are thinner and less useful as a template — prefer the riscv32 pair for coverage depth.
- Keep `test/03_system/os/qemu/sys_qemu_x86_32_fs_exec_spec.spl` as the Phase 3 system-level acceptance gate; it already exists and is written to never `skip()`, so it will stay red (accurately) until the backend lands.
- For arm32, add a new `test/03_system/os/qemu/sys_qemu_arm32_*_spec.spl` in Phase 3 if kernel integration is in scope, following the x86_32 test's structure (`os.qemu_systest_contract` helpers).

## 7. Risks

1. **Register allocator pressure assumption.** `regalloc.spl` is arch-agnostic today only because all 4 existing targets (x86_64, aarch64, riscv64, riscv32) have generous GPR counts. ARM32/AAPCS32 has 13 usable GPRs (r0–r12) and x86_32 has only 6–7 usable legacy GPRs (no r8–r15) — meaningfully tighter than any current target. Do not assume the existing heuristics "just work"; budget validation/tuning time.
2. **ARM32 encoding complexity underestimated.** Thumb2's mixed 16/32-bit instruction widths and A32's per-instruction condition codes make arm32 encoding structurally different from (not a subset of) AArch64's fixed-width A64 — treat it as a from-scratch backend at riscv32 scale, not a trim of `encode_aarch64.spl`.
3. **hal.spl import-closure bug is unscoped.** The existing comment flags a real, unresolved build-graph issue gating x86_32 (and all non-x86_64 arches) from the kernel build. Re-adding imports without first understanding this bug risks reintroducing whatever broke the build closure originally.
4. **ELF32 writer path is ad hoc.** The only existing ELF32 emission (`emit_elf32_riscv32` in `mod.spl`) was written narrowly for riscv32 and is unverified as a general ELF32 writer; x86_32 may need its own section/program-header layout rather than a clean shared function.
5. **No arm32 system test exists to gate correctness**, unlike x86_32 — without deliberately adding one in Phase 3, the arm32 backend has no forcing function to stay correct/maintained (x86_32's kernel tree sat disconnected until its QEMU test made the gap visible).

## Scope Note
This plan only covers the native codegen backend (isel/encode/ELF emission)
and its direct integration points (`mod.spl`, `target_presets.spl`,
baremetal linker/crt0 assets, kernel HAL wiring). It does not re-scope the
existing `feature_caps_arch32.spl`/`intrinsic_lowering_arm32.spl` capability
layer, which is already adequate for Phase 1/2 lowering decisions.
