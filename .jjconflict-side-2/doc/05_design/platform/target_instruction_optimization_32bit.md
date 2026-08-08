<!-- codex-design -->
# Target Instruction Optimization and 32-bit Support - Detail Design

Date: 2026-05-15

## Core data types

- `TargetFamily`: `X86_64`, `X86_32`, `Aarch64`, `Arm32`, `Rv64`, `Rv32`.
- `TargetFeatureSet`: normalized CPU, ABI, feature flags, strictness, optimization level.
- `InstructionFamily`: stable id plus target-family availability metadata.
- `FamilyDecision`: enabled boolean, disabled reason, source of decision, and fallback family.
- `LegalityProof`: records why a rewrite is semantically safe.

## Planner flow

1. Parse target triple and explicit flags.
2. Build or fetch cached `TargetFeatureSet`.
3. Evaluate all `InstructionFamily` records into a `TargetEnableMatrix`.
4. Run legality analysis for candidate MIR idioms.
5. Run profitability scoring.
6. Dispatch to target lowering only for enabled and legal families.
7. Emit diagnostics for skipped requested families.

## x86-64 32-bit-form rules

Allowed:

- Operations on values typed as `i32/u32`.
- Writes where high 32 bits are dead.
- Zero-extending writes whose consumers require unsigned 64-bit values.
- Immediate materialization where imm32 sign/zero behavior matches the type.

Rejected:

- Pointer values under LP64.
- Signed 64-bit values unless sign extension is explicitly preserved.
- Values crossing ABI boundaries without matching ABI extension rules.
- Mixed-width compares, shifts, divisions, and overflow-sensitive operations without proof.

## Native IA-32 milestone

Native x86-32 is a separate backend milestone:

- Add target dispatch and target presets.
- Add SysV i386 calling convention.
- Add 32-bit register allocation constraints.
- Add ELF32 object/relocation emission.
- Add QEMU/native runner smoke tests.
- Add golden instruction and ABI tests.

## ARM/RISC-V extension strategy

Start conservative. Every ARM/RISC-V family must have explicit feature detection and fallback. RV32/RV64 and ARM32/AArch64 are separate because ABI, pointer width, register names, and extension availability differ.

## Observability

Emit optional diagnostics:

- target family and feature-set hash,
- enabled/disabled family counts,
- disabled reasons,
- legality rejection counts,
- selected instruction-family counts,
- benchmark metadata for optimization-on/off comparisons.

