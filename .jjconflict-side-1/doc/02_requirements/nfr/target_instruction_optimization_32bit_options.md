<!-- codex-research -->
# Target Instruction Optimization and 32-bit Support - NFR Options

Date: 2026-05-15

## Option 1 - Correctness Gate Only

Require deterministic target enable/disable decisions, golden lowering tests, and strict unsupported-feature failures. No perf threshold.

Pros: fastest to implement.
Cons: does not prove the optimization is worth enabling.
Effort: S.

## Option 2 - Correctness Plus x86-64 Non-Regression

Require all Option 1 checks, x86-64 optimized mode runtime no slower than baseline within 3% median noise across representative benchmarks, and `.text` size no larger than baseline for targeted kernels.

Pros: directly addresses x86-64 speedup-or-same requirement.
Cons: requires stable benchmark harness and repeated runs.
Effort: M.

## Option 3 - Cross-ISA Competitive Benchmarking

Require Option 2 plus Simple-vs-C-vs-Rust comparisons on x86-64, x86-32, AArch64, ARM32, RV64, and RV32 where toolchains/emulators are available.

Pros: answers whether Simple is faster than C/Rust by target family.
Cons: expensive and may be inconclusive under QEMU; hardware availability matters.
Effort: L.

## Decision needed

Choose one NFR option before final NFRs are written. Recommended implementation path is Option 2 for the first milestone, with Option 3 as a tracked benchmark expansion.

