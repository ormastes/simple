<!-- codex-research -->
# Simple Compiler Performance and Memory Efficiency — Domain Research

Date: 2026-08-22. This document separates verified source claims from design inference for Simple.

## Optimizer facts and legality

LLVM loop fusion requires canonical loop structure and consumes dominance/post-dominance, ScalarEvolution, and dependence information; throwing instructions, atomics, volatile access, control incompatibility, and backward dependences can block fusion. LLVM's current documented fusion profitability hook is deliberately incomplete. [LLVM Loop Fusion](https://llvm.org/docs/LoopFusion.html) and [LLVM pass reference](https://llvm.org/docs/Passes.html).

LLVM MemorySSA represents memory definitions, uses, and phis and answers clobber queries using alias analysis. Its documentation explicitly contrasts this with memory-dependence approaches that can become quadratic and cautions against eagerly optimizing every memory definition. [LLVM MemorySSA](https://llvm.org/docs/MemorySSA.html).

Inference for Simple: shared CFG/dominance/loop/recurrence/dependence facts are a legality prerequisite, not an optimizer convenience. `MemorySSA-lite` should be region-based, demand-driven, cached, bounded, and fail closed on `Unknown`.

## Optimization remarks

LLVM distinguishes passed, missed, and analysis remarks, supports serialized machine output, filtering, and profile hotness. MLIR exposes opt-in structured passed, missed, failure, and analysis metrics and can use LLVM serialization. [LLVM Remarks](https://llvm.org/docs/Remarks.html), [MLIR Remarks](https://mlir.llvm.org/docs/Remarks/).

Inference for Simple: source warnings/errors, optimization remarks, and transform telemetry should share stable identities but remain distinct policy channels. Ordinary missed optimizations must not turn normal lint into warning noise or affect exit status.

## Low-cost performance and memory lint

Clang-tidy detects bounded repeated growth that can use `reserve` and avoidable copies, but documents lifetime limitations for copy-to-reference advice. Clippy provides configurable materialization, large-stack-array/frame, and large-enum-variant rules across opt-in profiles. [Clang reserve check](https://clang.llvm.org/extra/clang-tidy/checks/performance/inefficient-vector-operation.html), [Clang copy check](https://clang.llvm.org/extra/clang-tidy/checks/performance/unnecessary-copy-initialization.html), [Clippy lint index](https://rust-lang.github.io/rust-clippy/stable/index.html).

Inference for Simple: reserve/copy/materialization/layout checks fit a cheap typed-HIR tier. Fixes require mutation, lifetime, order, and collection-contract facts; layout thresholds must be target- and profile-aware.

## Escape explanations and allocation evidence

Go exposes compiler escape explanations and profiles allocation/live object counts and bytes. Profiling guidance distinguishes allocation rate from live heap. [Go GC guide](https://go.dev/doc/gc-guide), [runtime/pprof](https://pkg.go.dev/runtime/pprof), [Go compiler diagnostics](https://go.dev/doc/go1.14).

Inference for Simple: every `NoEscape` proof and failed promotion needs a source path/reason. Static site identity should connect to allocation count/bytes/lifetime profiles, but profile observations never prove semantic lifetime safety.

## Fusion and symbolic cost

Futhark research uses high-level producer-consumer and horizontal fusion; stream fusion eliminates intermediate lists through a representation that ordinary simplification can consume. [Futhark fusion](https://futhark-lang.org/publications/array16.pdf), [Stream Fusion](https://ora.ox.ac.uk/objects/uuid%3Ab4971f57-2b94-4fdf-a5c0-98d6935a44da/files/m73c0c572c3bb8bc7a2076ebc3378da95).

Infer Cost produces compositional symbolic cost summaries and differential complexity reports while returning unknown for unsupported callees. SPEED and Loopus demonstrate bounded loop/counter analyses. RaML/AARA demonstrates amortized resource inference and the need for explicit resource semantics. [Infer Cost](https://fbinfer.com/docs/checker-cost/), [SPEED](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/cav09_speed.pdf), [Loopus](https://arxiv.org/abs/1508.04958), [RaML](https://cs-www.cs.yale.edu/homes/hoffmann/papers/HoffmannW15.pdf), [AARA survey](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/two-decades-of-automatic-amortized-resource-analysis/9A47A8663CD8A7147E2F17865C368094).

Inference for Simple: CollectionPlan fusion should precede arbitrary MIR fusion. A bounded `CostExpr` must distinguish worst, expected, amortized, total allocation, and peak-live memory and propagate `Unknown(reason)` when caps are exceeded.

## Profile-guided repetitive work

Toddler reports loops with repetitive or partially similar memory-access patterns and uses context/filtering to reduce expected repetitions. [Toddler paper](https://people.cs.uchicago.edu/~shanlu/paper/icse13-preprint.pdf).

Inference for Simple: repetitive-access, false-sharing, retained-capacity, and AoS/SoA advice belongs in an offline/profile tier. It prioritizes candidates; it is not proof that a rewrite is legal or profitable.

## Consolidated constraints

1. One cached fact service feeds diagnostics, remarks, and transforms under explicit budgets and invalidation.
2. Unknown alias, lifetime, effect, recurrence, exceptional-flow, ordering, or profitability facts reject automatic rewriting.
3. Warnings identify likely actionable source defects; remarks explain optimization outcomes; policy errors enforce selected Robust/Critical contracts.
4. Total work, total allocations, allocated bytes, and peak-live memory are separate metrics.
5. High-level fusion comes first; general MIR fusion requires complete control, dependence, effect, numeric-order, and profitability evidence.
