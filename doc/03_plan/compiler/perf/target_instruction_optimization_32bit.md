<!-- codex-design -->
# Target Instruction Optimization and 32-bit Support - System Test Plan

Date: 2026-05-15

## Correctness

- Target matrix tests for x86-64, x86-32, AArch64, ARM32, RV64, and RV32.
- Strict-mode unsupported-feature tests.
- Compatibility-mode fallback tests.
- Golden MIR/lowering tests for each enabled instruction family.
- ABI tests for native IA-32 once that milestone starts.

## x86-64 non-regression

- Compile benchmark fixtures with optimization off and on.
- Compare runtime median across at least 10 runs.
- Require optimized mode to be faster or within 3% of baseline.
- Require targeted narrow-form kernels to keep `.text` size same or smaller.
- Track instruction bytes, selected family counts, and binary size.

## Cross-language benchmarks

Compare Simple, C, and Rust for:

- integer arithmetic loops,
- pointer-heavy traversals,
- hash/CRC kernels,
- memcopy/memset-like loops,
- bit operations,
- vectorizable numeric loops.

Use native hardware when available. QEMU results are acceptable for correctness and smoke, not final performance claims.

