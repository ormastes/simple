<!-- codex-design -->
# Agent Task Plan - Target Instruction Optimization and 32-bit Support

Date: 2026-05-15

## Task 1 - Target matrix owner

Files: `src/compiler/70.backend/feature_caps.spl`, target preset files, MIR opt context files.

Deliver:
- `TargetFamily` rows for x86-64, x86-32, AArch64, ARM32, RV64, RV32.
- Enable/disable matrix with disabled reasons.
- Unit tests for explicit feature toggles.

## Task 2 - Optimization planner owner

Files: `src/compiler/60.mir_opt/mir_opt/mod.spl`, `pattern_dispatch.spl`, plugin docs.

Deliver:
- Shared instruction-family registry.
- Cached planner keyed by target feature set.
- Provider filtering by target family and features.

## Task 3 - x86-64 narrow-form owner

Files: x86 native isel/encoder/lowering files.

Deliver:
- Legality checks for 32-bit-form selection.
- Golden tests for safe and rejected rewrites.
- Benchmark fixtures with optimization on/off.

## Task 4 - Native IA-32 owner

Files: native backend dispatch, x86-32 isel/encode, calling convention, ELF32 object emission.

Deliver:
- i386 SysV ABI lowering.
- 32-bit register allocation constraints.
- QEMU/native smoke tests.

## Task 5 - ARM/RISC-V family owner

Files: AArch64/ARM/RISC-V lowering and feature capability files.

Deliver:
- Conservative feature tables for ARM32/AArch64/RV32/RV64.
- Lowering hooks for bitmanip, crypto, scalar narrow forms, and vector/SIMD families.
- Fallback tests for unsupported features.

## Task 6 - Benchmark owner

Files: benchmark fixtures, test plans, CI scripts.

Deliver:
- x86-64 same-or-faster gate.
- Simple vs C vs Rust benchmark matrix.
- Clear distinction between hardware performance and QEMU smoke results.

