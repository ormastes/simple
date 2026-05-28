<!-- codex-research -->
# Optimization Plugin JIT Hotspot Domain Research

Date: 2026-05-24

## Findings

Modern optimizing runtimes separate compile-time optimization from runtime profile-driven optimization:

- A compiler pass pipeline can optimize ahead of time from static facts.
- A JIT uses profile facts such as hot counts, stable types, branch behavior, and guards to decide when a region is worth compiling or specializing.
- A correct JIT keeps a fallback path and deoptimizes or invalidates specialized code when runtime guards no longer hold.

## Implications For Simple

Simple Optimization Plugin should not be limited to compiler optimization. The same provider metadata should also describe runtime hotspot optimizers:

- Provider kind: `jit-hotspot`.
- Lookup kind: usually `pipeline-pass`, because hotspot planning is region/function scoped rather than per-symbol exact lookup.
- Required facts: runtime profile and guard facts.
- Produced facts: a hotspot plan, not an unconditional semantic rewrite.
- Safety: runtime-guarded; disabling the provider must preserve interpreter/native fallback behavior.

## Near-Term Constraint

The current repo has JIT integration docs and execution-manager references, but the safe first implementation is the provider contract and tests. Backend-specific hotspot compilation should be added after the contract is stable and after representative profile/invalidation tests exist.

## 2026-05-28 Backend Policy Research Addendum

Cranelift and LLVM should not receive identical Simple-side optimization plans:

- Cranelift positions itself as a fast, secure, relatively simple backend intended for JIT/AOT embedding. Its public project page explicitly describes a less aggressive optimization stance than LLVM/gcc and highlights compile speed, simplicity, correctness, and avoidance of historically risky optimization complexity such as advanced alias analysis. Source: https://cranelift.dev/
- Cranelift exposes coarse optimization levels (`none`, `speed`, `speed_and_size`) rather than a frontend-owned LLVM-style scalar optimization pipeline. Source: https://docs.rs/cranelift-codegen/latest/cranelift_codegen/settings/struct.Flags.html
- LLVM's documented frontend guidance for mutable variables recommends stack `alloca` plus optimizer promotion; LLVM `mem2reg`/SROA can convert allocas and aggregates into SSA values, and SROA is documented as more powerful than basic mem2reg. Source: https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl07.html
- LLVM SROA exists specifically to scalar-replace aggregates, and upstream source documentation describes converting non-escaping allocas into scalar SSA values. Source: https://llvm.org/doxygen/SROA_8h_source.html and https://llvm.googlesource.com/llvm-project/+/refs/tags/llvmorg-20.1.4/llvm/lib/Transforms/Scalar/SROA.cpp

Implication: Simple-side SSA/escape/borrow-informed canonicalization is most valuable before Cranelift or interpreter JIT planning, while LLVM-backed plans should be able to skip redundant or potentially compile-time-expensive Simple pre-optimization when LLVM will run equivalent scalar-promotion passes downstream.
