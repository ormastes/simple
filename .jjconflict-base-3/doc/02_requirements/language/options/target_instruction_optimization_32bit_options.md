<!-- codex-research -->
# Target Instruction Optimization and 32-bit Support - Feature Options

Date: 2026-05-15

## Option A - Conservative Target Matrix First

Add target-family capability rows for x86-64, x86-32, AArch64, ARM32, RV64, and RV32. Add plugin enable/disable by target and feature flags. Keep IA-32 native backend and x86-64 32-bit-form optimization as planned but not implemented in the first change.

Pros: lowest risk, unlocks clean planning and tests, minimizes duplication early.
Cons: does not immediately generate native IA-32 code or x86-64 32-bit-form speedups.
Effort: M, about 8-12 files plus docs/tests.

## Option B - Matrix Plus x86-64 32-bit-Form Optimization

Do Option A and add a guarded x86-64 optimization family that selects 32-bit instruction forms for proven safe `u32/i32` values, zero-extended values, narrow locals, and imm32 materialization.

Pros: delivers measurable x86-64 code-size/perf work while preserving backend structure.
Cons: requires legality verifier, golden tests, and perf gates.
Effort: L, about 15-25 files plus benchmark fixtures.

## Option C - Full IA-32 Native Backend Milestone

Do Option B and add native IA-32 target support: i386 SysV ABI, 32-bit register allocation constraints, ELF32 relocation/object emission, QEMU/native runner, and backend conformance tests.

Pros: satisfies complete 32-bit x86 native support.
Cons: highest risk; ABI/object/register allocation work is broad and can distract from plugin architecture.
Effort: XL, about 30-50 files plus runner infrastructure.

## Option D - Multi-ISA Optimization Expansion

Do Option B and implement first-class ARM32/RV32/AArch64/RV64 instruction families in parallel: bitmanip, crypto, scalar narrow forms, vector/SIMD families, and target-specific lowerers.

Pros: aligns all requested target families under one plugin architecture.
Cons: requires target hardware or emulation matrix and careful feature gating.
Effort: XL, about 35-60 files plus CI/emulator plan.

## Decision needed

Choose one feature option before final requirements are written. Recommended implementation path is B, then C/D as follow-up milestones.

