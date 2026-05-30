<!-- codex-research -->
# Target Instruction Optimization and 32-bit Support - Local Research

Date: 2026-05-15

## Scope

Research native x86 32-bit support, target-gated optimization plugin design, x86-64 use of 32-bit instruction forms where semantically safe, and extension points for ARM/RISC-V 32/64 targets.

## Existing repo shape

- `src/compiler/60.mir_opt/mir_opt/mod.spl` already has `OptimizationPipeline`, `OptimizationRuleProvider`, `TargetOptContext`, `TargetCapsKind`, `optimize_module_with_caps`, and `optimize_module_with_context`.
- `pipeline_optimize` already dispatches pattern idiom passes through a target context, with a special x86 path and generic capability path.
- `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` is the current target idiom dispatch surface.
- `src/compiler/70.backend/feature_caps.spl` defines `TargetIdiom`, `TargetFeatureClass`, `X86Caps`, `Aarch64Caps`, `Rv64Caps`, and cost helpers.
- `src/compiler/70.backend/lowering/` already separates intrinsic lowering by target family: x86, AArch64, and RISC-V.
- Existing backend docs already cover shared backend structure and SIMD strict emission:
  - `doc/04_architecture/simple_optimization_plugin.md`
  - `doc/04_architecture/compiler_optimization_infra_refactor_2026-05-13.md`
  - `doc/04_architecture/simd_backend_strict_emit.md`
  - `doc/05_design/backend_shared_architecture.md`

## Current gaps

- Native IA-32/i386 is not a first-class native backend path. Existing native x86 code is x86-64 oriented.
- The optimization capability model is mostly 64-bit-family oriented: x86-64, AArch64, RV64. x86-32, ARM32, and RV32 need explicit target families and conservative feature tables.
- x86-64 32-bit data-form selection is not represented as a late, semantics-checked optimization family.
- Target feature enablement needs a single matrix that can answer "enabled", "disabled", and "why" for each optimization family.
- Tests should verify both correctness and perf invariants:
  - x86-64 optimized builds are faster or statistically same as baseline.
  - x86-64 refactoring does not regress instruction selection.
  - x86-32/ARM32/RV32 feature toggles are conservative and deterministic.
  - Unsupported ISA features fall back or fail clearly, never silently emit unsupported instructions.

## Architecture implication

This should be implemented as an extension of the current MIR optimization plugin and backend lowering architecture, not as separate per-target optimizer forks. Shared legality, profitability, and plugin filtering should live above backend lowering. ISA-specific instruction emission and ABI details should stay in target modules.

