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

## 2026-05-28 General Optimization Recommendation Addendum

Primary-source follow-up:

- LLVM's New Pass Manager documentation recommends using `PassBuilder` default
  optimization pipelines for normal module optimization instead of manually
  duplicating a backend pipeline. Source: https://llvm.org/docs/NewPassManager.html
- LLVM frontend performance tips state that SROA and Mem2Reg eliminate allocas
  only under specific frontend shapes, especially entry-block allocas. Source:
  https://llvm.org/docs/Frontend/PerformanceTips.html
- Cranelift frontend SSA construction uses variables and block parameters for
  values crossing blocks; Simple should preserve high-level facts before that
  lowering point. Source:
  https://docs.rs/cranelift-frontend/latest/src/cranelift_frontend/ssa.rs.html

Implication: the plugin catalog needs a decision layer, not only raw passes.
LLVM should get a backend-managed default-pipeline recommendation and skip
Simple-side `ssa-var-canon`, while general high-level MIR optimizations such as
bounds-check elimination, delimiter scan recognition, and checksum reduction
remain useful for both LLVM and Cranelift because those facts are easiest to
prove before lowering into backend IR or runtime calls.

## 2026-05-28 Web Research Refresh

Primary-source refresh:

- LLVM's pass documentation lists `mem2reg`, SROA, GVN, LICM, loop unroll,
  vectorization-adjacent scalar passes, alias analyses, memory dependence, and
  scalar-evolution based analysis in the standard optimization surface. Source:
  https://llvm.org/docs/Passes.html
- LLVM's mutable-variable frontend tutorial states that `mem2reg` is
  alloca-driven, entry-block limited, direct-load/store limited, and that SROA
  handles aggregates that plain `mem2reg` cannot. It also recommends this
  alloca-plus-promotion approach for LLVM frontends unless there is a strong
  reason to construct SSA directly. Source:
  https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl07.html
- Cranelift's 2026 acyclic-egraph mid-end writeup describes a modern Cranelift
  pipeline that composes GVN, LICM, DCE, rematerialization, and algebraic
  rewrites, with explicit compile-time/execution-time tradeoffs. Source:
  https://cfallin.org/blog/2026/04/09/aegraph/

Implications for Simple:

- Keep LLVM plans focused on frontend IR shape and high-level semantic facts;
  do not duplicate LLVM-owned scalar promotion, inlining, vectorization, and
  loop-unroll pipelines in medium-budget JIT rebuilds.
- Keep Cranelift plans willing to run Simple-side SSA-var, bounds, delimiter
  scan, checksum, and local loop optimizations when those facts are available
  before backend lowering.
- Dynamic manifest rule execution must be gated by the same backend and
  compile-cost policy as descriptor selection, otherwise a skipped LLVM pass can
  still mutate MIR through generic pattern execution.
