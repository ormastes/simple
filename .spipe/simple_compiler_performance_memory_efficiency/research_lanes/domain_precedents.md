<!-- codex-research -->
# Domain precedents for compiler performance and memory-efficiency work

Research date: 2026-08-22. This lane uses official project documentation and original/author-hosted papers. “Verified” records what a source states; “Inference for Simple” is a design conclusion, not a claim made by the source.

## Optimizer analyses and reporting

### LLVM loop infrastructure

**Verified.** LLVM's loop-fusion implementation requires canonical loop structure and uses dominator/post-dominator information, ScalarEvolution (SCEV), and dependence analysis. Candidate loops must be control-flow compatible and adjacent; throwing instructions, atomics, and volatile accesses are hard blockers. Dependence direction is used to reject backward loop-carried hazards. The current documented profitability hook always returns beneficial, explicitly leaving a fuller cost model for future work. SCEV represents induction expressions and supplies trip-count and related loop facts. [LLVM Loop Fusion](https://llvm.org/docs/LoopFusion.html), [LLVM analysis/pass reference](https://llvm.org/docs/Passes.html)

**Inference for Simple.** General loop fusion must sit on shared CFG, dominance, canonical-loop, recurrence, effect, and dependence facts. Structural adjacency alone is insufficient. Legality and profitability should be separately reported; Simple should not copy LLVM's placeholder profitability policy into production.

### LLVM dependence and MemorySSA

**Verified.** LLVM dependence analysis distinguishes flow, anti-, and output dependences and represents loop-level directions. MemorySSA provides SSA-like memory definitions, uses, and phis; its walker answers and caches clobber queries using alias analysis. LLVM documents it as a replacement for use cases where MemoryDependenceAnalysis can easily produce quadratic algorithms, while also noting that eagerly optimizing every MemoryDef would itself be quadratic and is therefore avoided. [LLVM Loop Fusion, dependence section](https://llvm.org/docs/LoopFusion.html), [LLVM MemorySSA](https://llvm.org/docs/MemorySSA.html)

**Inference for Simple.** A bounded “MemorySSA-lite” with explicit regions and cached clobber queries is a sound architectural starting point. It must remain demand-driven and expose analysis limits; building all pairwise memory relations would defeat the compile-time objective.

### LLVM and MLIR optimization remarks

**Verified.** LLVM distinguishes `Passed`, `Missed`, and `Analysis` remarks, can serialize them as YAML or bitstream, can filter them by pass, and can attach profile hotness. MLIR's remark infrastructure is opt-in, streams structured metrics, supports `Passed`, `Missed`, `Failure`, and `Analysis`, and can use LLVM's serialization backend. [LLVM Remarks](https://llvm.org/docs/Remarks.html), [MLIR Remark Infrastructure](https://mlir.llvm.org/docs/Remarks/)

**Inference for Simple.** Optimizer telemetry should be structured and machine-readable, with success, missed-proof, failed-attempt, and neutral-analysis categories. It should be disabled or lazily constructed by default, and warnings/errors should remain reserved for source or policy problems rather than ordinary missed optimizations.

## Low-cost source lint precedents

### Clang-tidy

**Verified.** `performance-inefficient-vector-operation` recognizes bounded loops that repeatedly grow vectors or protobuf repeated fields and recommends `reserve`. `performance-unnecessary-copy-initialization` recommends a const reference only where uses permit it, but explicitly documents a limitation: it does not perform lifetime analysis and can suggest a dangling reference after invalidation. [Inefficient vector operation](https://clang.llvm.org/extra/clang-tidy/checks/performance/inefficient-vector-operation.html), [Unnecessary copy initialization](https://clang.llvm.org/extra/clang-tidy/checks/performance/unnecessary-copy-initialization.html)

**Inference for Simple.** Missing-reserve and avoidable-copy checks belong in the cheap typed-HIR tier, but fix-its need lifetime, mutation, and collection-contract gates. A diagnostic may remain advisory when those facts are unavailable.

### Rust Clippy

**Verified.** Clippy includes `needless_collect`, `large_stack_arrays`, `large_stack_frames`, `large_enum_variant`, and related performance/layout checks. Several are opt-in (`pedantic` or `nursery`) and use configurable size thresholds, demonstrating that source-level memory diagnostics benefit from policy profiles rather than one universal severity. [Clippy lint index](https://rust-lang.github.io/rust-clippy/stable/index.html#needless_collect), [large stack arrays](https://rust-lang.github.io/rust-clippy/stable/index.html#large_stack_arrays), [large stack frames](https://rust-lang.github.io/rust-clippy/stable/index.html#large_stack_frames), [large enum variant](https://rust-lang.github.io/rust-clippy/stable/index.html#large_enum_variant)

**Inference for Simple.** Materialization, frame, stack-array, and enum-layout rules should have target-aware thresholds and configurable profiles. Representation-changing advice should normally be a lint or remark, not an automatic semantic rewrite.

## Escape-analysis and profiling precedent

### Go

**Verified.** Go describes escape-to-heap as a lifetime decision, including transitive escape. `go build -gcflags=-m=3` explains compiler optimization and escape decisions; Go also exposes machine-readable optimization logs and editor overlays. Heap profiles distinguish allocation count/bytes and live count/bytes (`alloc_objects`, `alloc_space`, `inuse_objects`, `inuse_space`), and the official GC guide recommends allocation-rate views for finding GC-reduction opportunities. [Go GC guide](https://go.dev/doc/gc-guide), [runtime/pprof](https://pkg.go.dev/runtime/pprof), [Go 1.14 compiler diagnostics](https://go.dev/doc/go1.14)

**Inference for Simple.** Every failed promotion should retain an explainable escape path. Static escape reasons and dynamic allocation count/byte evidence should share site identifiers, but profile samples must not be treated as proof of non-escape or lifetime safety.

## Fusion precedents

### Futhark and stream fusion

**Verified.** Futhark research describes aggressive producer-consumer and horizontal fusion for high-level array operations. Stream fusion transforms list operations into a stream representation so ordinary compiler simplification can eliminate intermediate structures; the original work covers maps/folds, zips, nested lists, and list comprehensions and reports time/space improvements. [Futhark array fusion paper](https://futhark-lang.org/publications/array16.pdf), [Stream Fusion paper copy, Oxford Research Archive](https://ora.ox.ac.uk/objects/uuid%3Ab4971f57-2b94-4fdf-a5c0-98d6935a44da/files/m73c0c572c3bb8bc7a2076ebc3378da95)

**Inference for Simple.** A high-level CollectionPlan/producer-consumer fusion layer should precede arbitrary MIR loop fusion. It preserves cardinality, ordering, ownership, and callback-effect information longer and offers a clearer place to eliminate intermediate allocations.

## Symbolic and amortized cost analysis

### Infer Cost

**Verified.** Infer Cost assigns symbolic costs to IR instructions, produces procedure cost polynomials, and has a differential mode comparing saved cost reports. Its documentation demonstrates reporting a linear-to-quadratic regression. It returns unknown when a required call cost is unknown and documents limitations including affine interval bounds and lack of recursion support. [Infer Cost](https://fbinfer.com/docs/checker-cost/)

**Inference for Simple.** Baseline complexity regression is practical as a bounded CI tier. Unknown callees and exhausted budgets must yield explicit `Unknown`/incomplete evidence, never a successful complexity certification.

### SPEED and Loopus

**Verified.** SPEED combines invariant generation, counters, control-flow refinement, and user-defined quantitative functions to infer symbolic bounds for sequential procedures; its paper identifies memory as harder than monotonically increasing time because deallocation matters. Loopus abstracts imperative counter increments and resets with difference constraints and derives transition and variable bounds; its evaluation reports improved coverage and speed over compared tools on real C code. [SPEED paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/cav09_speed.pdf), [Loopus paper](https://arxiv.org/abs/1508.04958)

**Inference for Simple.** A deliberately bounded recurrence/cost domain can handle many useful loops without unrestricted theorem proving. Time, allocation bytes, allocation count, and peak live bytes must be distinct resources; allocation totals cannot stand in for peak memory.

### RaML and AARA

**Verified.** RaML integrates multivariate automatic amortized resource analysis with an OCaml compiler and derives polynomial bounds over input sizes. AARA uses potential-based, local inference rules and numeric constraint solving; the research has expanded from linear heap bounds to polynomial and other resource metrics with operational-cost soundness arguments. [RaML paper](https://cs-www.cs.yale.edu/homes/hoffmann/papers/HoffmannW15.pdf), [AARA survey](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/two-decades-of-automatic-amortized-resource-analysis/9A47A8663CD8A7147E2F17865C368094)

**Inference for Simple.** Amortized annotations in the cost algebra are justified for collection growth, but claims used as hard CI gates require a stated cost semantics and a falsifiable proof/certificate boundary. A lightweight editor analysis should prefer `Unknown` over expensive constraint solving.

## Dynamic repetitive-work precedent

### Toddler

**Verified.** Toddler is a dynamic performance-bug oracle that reports loops with repetitive and partially similar memory-access patterns across iterations. Its Java evaluation covered known bugs and reported newly discovered issues. It records loop/test/call-stack context and applies filters to reduce expected repetitive reads. [Toddler paper, author-hosted preprint](https://people.cs.uchicago.edu/~shanlu/paper/icse13-preprint.pdf)

**Inference for Simple.** Repetitive-access detection belongs in the profile-guided/offline tier, not the default lint. Reports should include site, loop, call path, repetition statistics, and suppression/filter rationale; similarity is a candidate signal, not proof that work is unnecessary.

## Consolidated design constraints derived from the precedents

These are synthesis, not direct source claims:

1. Use one cached fact service for CFG/dominance/loops/def-use/memory/effects/cardinality; transformations and diagnostics query it under explicit budgets.
2. Keep source warnings, optimization remarks, transformation telemetry, and policy errors distinct even when they share rule identifiers.
3. Fail closed for semantic transformations: unknown alias, lifetime, effect, recurrence, exceptional-control-flow, or ordering facts reject the rewrite and may produce a missed remark.
4. Make complexity analysis compositional but bounded; propagate `Unknown(reason)` and analysis-incomplete status.
5. Separate total work/allocation from peak live memory and distinguish expected, amortized, and worst-case claims.
6. Prefer high-level pipeline fusion first; general MIR fusion requires stronger control-flow and dependence proof plus a real profitability model.
7. Link static site identities to profiles, while treating runtime evidence as prioritization/profitability input rather than equivalence proof.
