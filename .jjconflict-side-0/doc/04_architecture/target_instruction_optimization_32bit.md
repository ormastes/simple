<!-- codex-design -->
# Target Instruction Optimization and 32-bit Support - Architecture

Date: 2026-05-15

## Goal

Extend the existing optimization plugin and backend capability architecture so target-specific instruction families can be enabled, disabled, tested, and lowered for x86-64, x86-32, AArch64, ARM32, RV64, and RV32 with minimal duplication.

## Layers

1. Target identity layer:
   - Normalize target triple, ABI, CPU, and explicit feature flags.
   - Represent `x86_64`, `x86_32`, `aarch64`, `arm32`, `riscv64`, `riscv32` as separate target families.

2. Capability matrix layer:
   - Add `InstructionFamily` records with `id`, `target_family`, `required_features`, `forbidden_features`, `safety`, `cost`, and `fallback`.
   - Return `Enabled` or `DisabledReason` for every family.
   - Cache the matrix per target configuration.

3. Legality layer:
   - Prove semantic safety before rewriting MIR or selecting narrower instruction forms.
   - For x86-64/AArch64 32-bit forms, require known-zero high bits, dead high bits, explicit narrow type, or ABI-approved extension.
   - Reject pointer truncation unless target ABI is explicitly ILP32/x32 or native 32-bit.

4. Profitability layer:
   - Use instruction cost, code-size cost, register pressure, and target feature hints.
   - Default to no rewrite when cost is unknown.

5. Dispatch and lowering layer:
   - Shared planner picks families.
   - Target lowerers emit ISA-specific forms.
   - ABI/object emission remains backend-specific.

## Instruction families

- Shared scalar: narrow ALU, imm32 materialization, sign/zero extension folding, shift/mask idioms, branchless select when available.
- x86-64: 32-bit ALU forms, LEA idioms, BMI1/BMI2, LZCNT/POPCNT, AES-NI, PCLMULQDQ, SSE2/SSSE3/SSE4, AVX/AVX2/AVX-512 gated by features.
- x86-32: scalar i386 baseline, SSE2 where requested, CMOV, POPCNT/LZCNT/BMI only when target CPU/features allow; no x86-64-only registers or ABI assumptions.
- AArch64: W-register narrow forms, NEON, CRC32, AES/SHA/PMULL, SVE/SVE2 gated by features.
- ARM32: ARMv7/Thumb-2 scalar, NEON/VFP, DSP, CRC, crypto extensions only when explicit.
- RV64/RV32: `M/A/F/D/C`, `Zba/Zbb/Zbs/Zbc`, `Zk*` crypto, `V`/`Zve*`, and code-size extensions gated by extension string/profile.

## MDSOC decision

Use a virtual capsule around target optimization planning:

- Shared capsule: `TargetOptimizationPlanner`.
- Feature transforms: each instruction family contributes legality, cost, and lowering hooks.
- Target capsules: x86, ARM, RISC-V implement only backend-specific lowering and ABI constraints.

This keeps cross-cutting optimization policy shared while preserving target encapsulation.

## Risk controls

- Unsupported requested features fail in strict mode and warn/fallback in compatibility mode.
- No optimization family may emit instructions outside the enabled matrix.
- No per-request or per-function rebuild of the capability matrix.
- x86-64 refactor must be same-or-faster or disabled by default.

