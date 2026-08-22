# Simple compiler performance and memory-efficiency audit

<!-- codex-research -->

Repository scope: static audit of ormastes/simple main at commit 37bd406e219cc35cae049b4130f5167c21801864, dated August 22, 2026 KST.

I inspected the lint path, collection analysis, MIR optimization registry and dispatch, loop analyses, vectorization, bounds-check elimination, and escape analysis. This was a source-level audit; I did not execute the compiler, test suite, or benchmarks. Findings below therefore distinguish observed code, derived risk, and runtime impact requiring measurement.

Executive conclusions

1. The highest-priority performance defect is not a missing loop lint. It is optimizer activation integrity. The Speed and Aggressive pipelines register many conventional scalar and loop optimizations, but at least eleven canonical function-level pass wrappers return the original MirFunction unchanged. The compiler currently advertises transformations that often do not run.


2. Do not activate all those implementations with a mechanical one-line change. Several dormant implementations are incomplete, inefficient, or potentially unsound. Each pass needs an activation contract, positive sentinel test, semantic differential test, and explicit Active / AnalysisOnly / Skeleton / Disabled status.


3. Simple already has the correct conceptual direction for collection complexity. Its CollectionPlan design reserves rules for nested dynamic iteration, repeated linear lookup, materialization, sorting, Cartesian products, missing indexes, and complexity regression. The gap is implementation and shared analysis infrastructure, not another disconnected lint framework.


4. Multiple loops are not inherently a bug. Fusion is legal only with compatible iteration spaces, dependence proofs, alias proofs, and effect/order preservation. It is profitable only when the saved traversal and eliminated intermediates outweigh increased register pressure, code size, and possible loss of vectorization.


5. Use four analysis tiers: cheap local editor lints, intraprocedural MIR analysis and optimization remarks, bounded interprocedural CI analysis, and profile-guided runtime feedback. All tiers should consume one cached PerfFacts service rather than repeatedly parsing or rebuilding CFG, loop, and alias information.




---

1. Important repository findings

1.1 Current optimizer truth table

The canonical Speed and Aggressive pipelines list DCE, constant folding, copy propagation, GVN, CSE, TCO, loop transformations, bounds-check elimination, vectorization, collection optimization, string building, outlining, and other passes. Dispatch resolves these names to typed PassKind values, but many wrappers are identities.

Pass or pass family
Current audited state
Consequence
Recommended status

Dead-code elimination
Implementation exists; public dispatch wrapper returns func unchanged.
No normal MIR DCE through this route
Disabled until liveness is redesigned
Constant folding
Wrapper returns input unchanged.
Constant expressions remain for later backend optimization
Skeleton pending overflow/FP/trap tests
Copy propagation
Wrapper returns input unchanged. The audited file did not expose a complete copy-map construction path.
Redundant copy chains survive
Skeleton
Local CSE
Wrapper returns input unchanged.
No Simple-native local CSE through canonical dispatch
Skeleton
GVN
Wrapper returns input unchanged. The implementation approximates dominator order with block order.
No GVN now; activation would require dominance correctness
Disabled
LICM and unrolling
Wrapper returns input unchanged.
General loop invariant motion and unrolling do not run
Disabled
Bounds-check elimination
Wrapper returns input unchanged.
No Simple-native BCE through this pipeline
Disabled; current proof scope is unsafe
Strength reduction
Wrapper returns input unchanged.
No native strength reduction
Disabled until signed/range proofs exist
String-builder transform
Wrapper returns input unchanged.
Repeated string concatenation is not transformed here
Disabled; transform construction is incomplete
Generator state-machine pass
Wrapper returns input unchanged.
No transformation through canonical dispatch
Skeleton
Tail-call optimization
Wrapper returns input unchanged.
Tail calls are not converted through this route
Disabled; parallel argument assignment required
Typed-byte canonicalization
Both class body and wrapper are explicit skeletons returning the input.
No widening of byte accesses
Skeleton
Body outlining
Function wrapper is an identity; module wrapper iterates with an empty pass_dn body.
Effectively no outlining
Skeleton
Auto-vectorization
Canonical dispatch is documented as pattern matching and logging only, with no production MIR rewrite.
Useful as analysis scaffolding, not an optimizer yet
AnalysisOnly
Collection optimization
Active; wrapper calls the me optimize_function implementation.
Some collection patterns genuinely transform MIR
Active, but requires legality audit
Module inlining
Module-level wrapper invokes ModuleInliner; function wrapper itself is an identity.
Cross-function module inlining can run
Active, with size/semantic gates


Recommended compiler self-lint

Add a compiler-internal rule:

COMP-PERF001 registered_transform_is_identity

It should fail CI when all of these are true:

A pass is registered as a transformation.

It appears in a canonical optimization pipeline.

Its dispatch wrapper unconditionally returns the input.

It is not explicitly marked Skeleton, Disabled, AnalysisOnly, or RemarkOnly.


The pass descriptor should become structurally honest:

enum PassStatus:
    Active
    AnalysisOnly
    RemarkOnly
    Skeleton
    Disabled(reason: text)

enum PassExpectation:
    MayTransform
    MustTransformSentinel
    NeverTransforms

This prevents “implemented-looking but inactive” code from silently accumulating again.


---

1.2 Dormant implementations must not be activated blindly

Component
Source-level blocker
Risk after naive activation

DCE
is_instruction_result_used scans later instructions for every definition, giving quadratic block behavior, and ultimately returns true on the no-use path to conservatively assume an inter-block use.
Almost no useful result DCE, with potentially high compile-time cost
CSE/GVN
Expression identities are encoded as interpolated text keys. GVN walks block order instead of a real dominator tree.
Compiler allocations and hashing on every expression; invalid reuse across non-dominating paths
LICM
The general loop pass is inactive, and the active collection optimizer inserts “hoisted” instructions into the loop header, not a true preheader. The loop detector defines the header as part of the loop.
Work may still execute every iteration; zero-trip execution can change if an operation is not speculatable
Bounds checks
Proofs are gathered from local instruction shapes and pre-seeded globally for block processing rather than attached to a dominated loop region.
A check outside the proof’s scope could be removed
Vectorization
“Step is one” detection accepts any constant, and it may find the increment in an unrelated block elsewhere in the function.
Incorrect vector loop bounds if rewriting is enabled
String builder
The implementation describes pre-loop builder initialization and post-loop join, but the shown transformation primarily replaces concatenation with push; the complete lifetime/result construction is not present in the audited path.
Undefined builder local or missing final string
TCO
Parameters are reassigned sequentially from recursive-call arguments.
Calls such as f(a,b) -> f(b,a) can clobber an argument unless all new values are first stored in temporaries
Strength reduction
Signed division and remainder by powers of two are not generally equivalent to arithmetic shifts/masks for negative operands. The provider mentions non-negative or unsigned facts, but activation must enforce them at each rewrite.
Wrong results for signed negative values
Body outlining
The module wrapper does not process functions before adding generated functions.
Remains a no-op even after being selected


The correct process is pass-by-pass rehabilitation, not bulk activation.


---

1.3 Current compile-time performance problems

Finding
Evidence
Classification
Corrective direction

Lint parsing dominates execution
The open lint performance investigation attributes roughly 99% of size-dependent time to parse_module_silent_checked, with checks themselves around 1%.
Observed measurement in repository report
Reuse daemon/compiler parse and typed-HIR artifacts; never launch an independent frontend for performance lints
Full-repository path deduplication was quadratic
CLI lint changed array membership to dictionary-based sets for tens of thousands of paths.
Observed fixed bug
Generalize cost-aware collection primitives and lint compiler code for linear membership in growing loops
Loop detection repeatedly rebuilds graph data
For each candidate header, reachability helpers rebuild successor or predecessor maps. Worklist pop uses array slicing.
Observed structure; allocation cost is derived
Build CFG, predecessors, RPO, dominators, and loop forest once per function
Vectorizer def-use construction contains nested definition/use loops
Dependencies are built with definitions × uses comparisons and repeated array concatenation.
Observed structure
Linear def-use lists plus SSA/use chains; append into owned buffers instead of uses = uses + ...
Several analyses build textual hash keys
CSE and GVN serialize expression identity to strings.
Observed
Interned structural keys such as (opcode, VN, VN, type, flags)
Passes rebuild overlapping facts
Loop detection, collection optimization, BCE, and vectorization contain separate loop/bounds/dependence logic.
Derived architectural issue
Shared immutable analysis results with explicit invalidation


LLVM’s current architecture offers useful precedent: ScalarEvolution provides induction and trip-count reasoning, DependenceAnalysis handles loop dependences, and MemorySSA gives efficient SSA-like memory queries rather than repeated instruction scans. LLVM documents MemorySSA partly as a response to memory-dependence approaches that could easily become quadratic.


---

1.4 Escape analysis is not ready to place allocations

Simple’s escape analysis has a useful state model—NoEscape, argument, return, field, global, and unknown escape—but several current behaviors block safe stack promotion:

The design says unknown values should be treated conservatively as escaping, but finalization changes remaining Unknown states to NoEscape.

Return handling is incomplete.

Field points-to keys do not appear consistently formed between store and load paths.

Allocation size is represented but not fully propagated to threshold decisions.

Points-to collections use arrays and repeated membership checks.

Repository planning still describes backend stack-allocation integration as deferred.


This is potentially unsound if the result is later used for allocation placement. It is not evidence of a current stack-lifetime miscompile while promotion remains unwired.

Before stack promotion:

1. Unknown must remain escaping.


2. Return, aggregate, closure capture, indirect call, field, and global flows must be complete.


3. Every NoEscape result must carry a proof reason.


4. Allocation size and alignment thresholds must be enforced.


5. Differential GC-root and lifetime tests must compare heap and promoted forms.


6. An unknown external call must fail closed unless an imported effect/escape summary is verified.



Go provides a good usability precedent: compiler diagnostics explain why a value escapes, while allocation profiles expose both object counts and allocated bytes.


---

2. Recommended analysis architecture

Do not create separate logic for the lint command, optimizer, IDE, and CI. Build one queryable fact layer over cached typed HIR and MIR.

2.1 Shared PerfFacts

struct PerfFacts:
    cfg: CfgFacts
    dominators: DominatorTree
    loops: LoopForest
    inductions: [InductionFact]
    def_use: DefUseFacts
    memory: MemorySsaLite
    aliases: RegionAliasFacts
    effects: EffectFacts
    cardinalities: CardinalityFacts
    costs: CostFacts
    allocations: AllocationFacts
    layouts: LayoutFacts

Simple already carries useful MIR effects such as computation, I/O, wait, allocation, filesystem, network, and unsafe behavior. Extend those effects quantitatively instead of inventing a parallel annotation system.

LoopForest

Build once per function:

LoopFact
    header
    preheader?
    latch set
    body bitset
    exits
    parent?
    children
    depth
    trip_count: Exact | UpperBound | Unknown
    induction: start, step, bound, signedness, nowrap proof

Important rules:

A bound such as i < 100 is not an exact trip count without proving the initial value and step.

Block IDs or storage order must never substitute for dominance or CFG order.

A transform requiring a preheader must create or verify a real preheader.

Irreducible loops should normally produce remarks, not transformations.


MemorySSA-lite

Start with regions rather than full pointer theorem proving:

enum Region:
    Stack(local)
    UniqueObject(allocation_site)
    Argument(index)
    Global(symbol)
    Device(resource)
    Unknown

The ownership model can make this substantially simpler:

An iso/unique value can provide a strong no-alias region.

An immutable shared value permits reads but no writes.

A mutable borrow identifies its exclusive region.

Raw or unsafe pointers collapse to Unknown unless a contract proves more.


Each load is connected to a dominating memory definition or phi. Unknown calls clobber Unknown; verified function summaries name their read and write regions. This single service supports DCE, CSE, LICM, fusion, bounds elimination, vectorization, and escape reasoning.


---

2.2 Machine-readable operation registry

Simple’s existing CollectionPlan proposal already points toward a shared operation registry and separate cost, effect, cardinality, order, and uniqueness summaries. Implement that as the common source of truth.

OperationSummary
    effects:
        reads, writes, allocates, throws, waits, io, atomic, unsafe
    time:
        worst: CostExpr
        expected: CostExpr?
    allocation_count:
        CostExpr
    allocation_bytes:
        CostExpr
    peak_live_bytes:
        CostExpr?
    output_cardinality:
        CardinalityExpr
    access:
        sequential | random | hash | tree | unknown
    order:
        preserved | reordered | unspecified
    uniqueness:
        unique | may_duplicate | unknown
    invalidation:
        receiver_mutation | global_epoch | immutable

Example entries:

Operation
Time
Allocation
Cardinality

Array.contains(x)
Size(receiver)
0
scalar
Dict.contains(x)
expected constant; worst linear
0
scalar
Array.keys/values/materialize
Size(receiver)
proportional to receiver
same size
sort
n log n
implementation-dependent temporary bytes
n
filter
n
up to n elements when eager
[0,n]
flat_map
sum of inner cardinalities
proportional to output
potentially product
immutable a + b
len(a)+len(b)
result size
sum
push
amortized constant
occasional growth
n+1


Keep expected and worst-case costs separate. Mission-critical analysis should not silently treat expected hash lookup as a hard constant bound.


---

2.3 Cost algebra

For editor lints, exact resource polynomials are unnecessary. Use a bounded symbolic algebra:

CostExpr =
    Const(value)
    Size(symbol)
    Add(parts)
    Mul(parts)
    Max(parts)
    Log(expr)
    Amortized(expr)
    Expected(expr)
    Unknown(reason)

Canonicalize and hash-cons expressions. Cap:

expression depth,

polynomial degree,

number of independent size variables,

recursive SCC iterations,

path splits.


When the cap is exceeded, produce Unknown, not an unreliable result.

For each loop:

loop_cost = trip_count * body_cost
loop_allocations = trip_count * body_allocations

For each call, substitute the callee’s size parameters. Recursive SCCs use bounded fixed-point summaries. Infer Cost, SPEED, Loopus, and RaML/AARA demonstrate complementary approaches for symbolic execution cost, loop-bound inference, and amortized time or space analysis.


---

3. Analysis tiers: fast enough for compiler and lint

The percentages below are design budgets, not measured Simple results.

Tier
Default use
Analysis
Target marginal overhead
Failure behavior

Tier 0: Local
Editor and normal simple lint
Typed-HIR walk, local type/layout and operation summaries; no call graph
≤2–3% after frontend reuse
Suppress uncertain findings
Tier 1: Function
Release compile and --perf-fast
CFG, dominators, loop forest, def-use, MemorySSA-lite, escape facts
≤5% release compile
Emit optimization remarks for unknown proofs
Tier 2: Program
Robust/Critical CI
Bounded call graph SCC summaries, symbolic cost/cardinality, baseline comparison
Explicit node/time budget
Report analysis incomplete, never silently certify
Tier 3: Profile-guided
Offline optimization
Hotness, allocation lifetime, repetitive memory access, cache/layout evidence
Outside normal compile path
Feed evidence into Tier 1 decisions


Because parsing currently dominates lint time, Tier 0 must run inside the existing compiler session or daemon and consume the same parse/HIR artifacts. A second parser process would erase most gains from keeping the checks lightweight.


---

4. Multiple-loop and algorithmic-complexity detectors

The repository already reserves COLL009 through COLL018 for most of the highest-value cases, while the actual source lint currently implements the earlier local-pattern rules and COLL019.

4.1 Recommended detector table

Rule
Pattern and analysis
Typical cost symptom
Compiler or lint
Tier

LOOP001 adjacent_same_domain
Adjacent loops over the same proven iteration domain; compare bounds, directions, early exits, effects, and dependence graph
Two or more full traversals
Auto-fuse only with complete legality and profitability proof; otherwise missed-optimization remark
1
COLL009 nested_dynamic_iteration
Dynamic loop nested under another dynamic loop; multiply symbolic trip counts
O(n*m) or O(n²)
Warning only when both dimensions may grow; suppress fixed small inner loops
0/1
COLL010 functional_linear_lookup
contains, find, index_of, or linear get inside a loop; operation registry supplies receiver complexity
O(n*m)
Suggest temporary index or Dict; normally no auto-fix because order, hashing, and memory change
0/1
COLL011 repeated_materialization
keys, values, collect, to_array, flatten, conversion, or clone inside a loop
Repeated O(m) time and allocation
Hoist/elide when receiver and semantics are invariant; otherwise warning
0/1
COLL012 sequential_indexing
Repeated nth(i) or generic indexing on linked, UTF-8, compressed, or iterator-backed data
Often O(n²)
Suggest iterator traversal; compiler rewrite only for exact semantics
0
COLL013 repeated_sort
Sort or ordered-index construction occurs inside an outer loop or repeats on unchanged input
O(n*m log m)
Hoist if immutable and comparator pure; otherwise warning
1
COLL014 unbounded_flat_map
flat_map/nested production whose inner cardinality is input-dependent
Output and allocation can become n*m
Warn with cardinality expression; Robust may require an explicit bound
1/2
COLL015 accidental_cartesian_product
Nested loops over unrelated collections with no recognized key relation or bounded side
O(n*m) and product output
Warning; recognize deliberate cartesian_product API or annotation to suppress
1
COLL016 missing_index
Stable collection repeatedly searched by the same key projection
Repeated linear lookup
Suggest one-time Dict/index construction with time-memory tradeoff
1
COLL017 complexity_regression
Compare canonical cost summary against main/baseline; detect new size variable or higher polynomial degree
O(n) → O(n²), allocations 0 → n
CI policy, not editor warning
2
COLL018 unknown_hot_callback_cost
Dynamic/virtual/function-value callback inside a dynamic loop lacks a verified summary
Unknown multiplier
Remark by default; warning only in hot/Robust code
1/2
LOOP019 repeated_reductions
Separate sum, count, min, checksum, or predicate scans over the same producer
Multiple traversals
Fuse accumulators if callbacks are pure and each reduction order is preserved
1
LOOP020 count_then_consume
Count/length scan followed by a second traversal, especially on non-sized iterables
Two passes or forced materialization
Use exact-size metadata, single-pass builder, or reserve upper bound
0/1
LOOP021 invariant_setup
Regex compilation, parser/serializer construction, format-plan creation, table building inside loop
Large constant work multiplied by n
Hoist with purity/lifetime proof; otherwise warning
0/1
LOOP022 effect_per_iteration
I/O, database, RPC, filesystem metadata, or device command in a loop
N+1 traffic or syscall amplification
Warning with batching/prefetch candidate; no generic compiler auto-fix
0/1
LOOP023 contention_per_iteration
Lock acquisition, blocking wait, or strong atomic operation inside a loop
Contention and serialization
Warning; Critical policy may deny blocking effects in marked paths
0/1
LOOP024 recursive_loop_multiplier
Recursive SCC contains a dynamic loop or calls a looping function per recursion level
Potential exponential or high polynomial behavior
Tier-2 cost analysis; editor only shows local hint
2
LOOP025 missed_vectorization
Canonical numeric loop not vectorized; report precise blocker
Scalar hot loop
Optimization remark, never a generic warning
1/3
LOOP026 repeated_same_source_pipeline
Eager map().filter().map() or several named temporaries consumed once
Traversal and intermediate allocation
CollectionPlan fusion when callbacks/effects permit
0/1


Important suppression rules

A nested or repeated loop should not warn merely because it exists. Suppress when:

The inner bound is a small compile-time constant.

The loop is cold and profiling confirms negligible cost.

Repeated passes are independently vectorized and fusion is predicted to regress throughput.

Fusion would increase live values beyond a register-pressure budget.

Separate passes improve locality through blocking or tiling.

The user explicitly chose a data structure preserving order or worst-case behavior.

The operation is bounded by a declared protocol or hardware maximum.



---

5. Memory-inefficiency detectors

5.1 Static and profile-guided rules

Rule
Pattern
Required facts
Action
Tier

MEM001 allocation_in_dynamic_loop
Heap allocation, collection creation, closure allocation, boxing, formatting buffer inside a dynamic loop
Allocation effect + loop multiplicity
Warn; automatically scalar-replace or stack-promote only with complete lifetime proof
0/1
MEM002 missing_reserve
Known exact or upper iteration count followed by repeated push/emplace into an empty/growing collection
Trip count, existing capacity, growth policy
Insert exact reserve when semantically invisible; otherwise fix-it
0/1
MEM003 repeated_concat_growth
String/array immutable concatenation into the accumulator in a loop
Ownership and resulting size
Builder transformation after correctness completion; warning today
0
MEM004 needless_materialization
Owned temporary collection is immediately iterated, counted, or searched once
Def-use and escape facts
Fuse producer/consumer or use view/iterator
0/1
MEM005 unnecessary_clone_or_copy
Large value cloned/copied while source remains available and immutable
Type size, move/borrow eligibility
Fix-it to borrow/move; compiler copy elision where exact
0
MEM006 copied_loop_item
Iteration binds a large element by value instead of reference
Element layout and mutation intent
Lint/fix-it
0
MEM007 large_value_parameter
Large aggregate passed or returned by value repeatedly
ABI lowering, size, call frequency
Suggest borrow/out parameter only when API semantics permit; compiler can optimize internal ABI
0/1
MEM008 pointer_rich_small_elements
Array<Box<small T>>, boxed collection, or one allocation per small node
Layout, object size, polymorphism
Suggest contiguous representation; no automatic public semantic change
0
MEM009 large_enum_variant
One sum-type variant dominates total size and most values use smaller variants
Variant sizes and profile frequencies
Suggest boxing/splitting the rare variant; compiler layout optimization only behind stable ABI rules
0/3
MEM010 large_stack_frame
Static arrays, inlined temporaries, spills, or generator state exceed target threshold
Post-layout frame estimate
Warning; optimizer may undo inlining or move cold storage
1
MEM011 zero_fill_then_overwrite
Allocation is zeroed and all bytes are definitely written before any read
Definite initialization, aliasing, trap paths
Eliminate zeroing automatically with full-overwrite proof
1
MEM012 temporary_buffer_pipeline
Temporary buffer is produced and consumed once without escaping
Def-use, effects, cardinality
Fuse, stream, or allocate in arena/stack
1
MEM013 retained_capacity_spike
Long-lived collection grows to a high watermark and then remains mostly empty
Escape/lifetime plus profile
Profile-guided remark; suggest shrink or bounded pool
3
MEM014 heap_escape_reason
Local allocation cannot be promoted
Escape path
Explain the exact store/call/return that caused escape
1
MEM015 repeated_format_or_serialize_buffer
Formatting/serialization repeatedly creates scratch buffers
Operation registry, loop multiplicity
Reuse builder or caller-owned scratch region
0/1
MEM016 index_rebuilt_in_loop
Hash table, sorted index, prefix table, or lookup cache recreated each iteration
Invariance and mutation facts
Hoist or warn
1
MEM017 oversized_closure_capture
Closure or async state captures a large aggregate by value
Capture layout and use set
Capture selected fields or reference where lifetime permits
0/1
MEM018 padding_waste
Struct or array element has large internal/tail padding
Target layout and ABI exposure
Layout remark; source fix-it can reorder private fields
0
MEM019 possible_false_sharing
Independently mutated fields used by different workers share a cache line
Ownership/thread-role evidence and target cache line
Concurrency/layout warning; padding only with explicit policy
1/3
MEM020 AoS_SoA_mismatch
Hot loop reads one or two fields from a large array-of-struct element
Access profile, layout, SIMD target
Profile-guided data-layout remark or generated SoA view
3
MEM021 allocation_churn_cluster
Many short-lived allocations at the same site or repeatedly across a pipeline
Allocation profile and lifetime histogram
Arena, folding, pooling, scalar replacement, or stack promotion candidate
3
MEM022 unbounded_retained_collection
Global, actor, service, or cache collection grows without eviction/bound
Escape and mutation summary
Existing COLL008-style warning; Robust/Critical can require an explicit bound
0/2


Clang-tidy already demonstrates low-cost source checks for missing reserve and avoidable copies, while Clippy includes checks for needless collection, oversized stack allocations, large stack frames, and related representation problems.


---

6. Compiler transformation versus lint or remark

Opportunity
Automatic compiler transform
Lint or remark
Reason

Constant folding and dead pure computation
Yes, after semantic correctness
Usually no source warning
Pure implementation detail
Copy elision and scalar replacement
Yes
Explain missed reason when hot
No source-level semantic choice
Exact reserve for an internal collection
Yes
Fix-it when public/custom collection behavior is uncertain
Capacity usually unobservable, but custom allocators may matter
Dead intermediate collection
Yes when non-escaping and effects preserved
needless_materialization warning otherwise
Strong producer-consumer proof
Pure map/filter pipeline fusion
Yes when callback effects and order are safe
Missed-fusion remark otherwise
Eager callbacks can have observable ordering
Adjacent general loop fusion
Yes only with complete dependence/effect proof and positive cost model
Missed-fusion remark
Interleaves iterations and can alter effects
Stack promotion
Yes only for proven NoEscape, bounded size, and valid lifetime
Escape explanation
Wrong proof is memory unsafety
Bounds-check elimination
Yes with dominance-scoped range proof
Missed proof remark
Safety-critical transform
Zero-fill removal
Yes with definite full initialization
Missed proof remark
Reads on exceptional paths must be excluded
Build a hash index for repeated lookup
Usually no
Suggestion with time/memory/order tradeoff
Hash/equality/order/worst-case behavior may change
Change array to linked structure or vice versa
No
Suggestion
Public semantics and memory behavior change
Batch database/RPC operations
No generic rewrite
Warning
Transaction, ordering, and failure semantics are domain-specific
Change lock granularity
No
Warning
Concurrency semantics
Box a large enum variant
Normally no source-independent rewrite
Layout lint
ABI, allocation, and identity may change
Split AoS into SoA
Profile-guided specialization or generated view only
Remark
Major representation/API choice
Pretenure or pool allocations
Runtime/PGO decision
Profile remark
Lifetime is workload-dependent


LLVM’s optimization-remark model is a good interface: distinguish successful transformations, missed transformations, and analysis details, and optionally attach profile hotness. MLIR similarly supports structured, opt-in remarks without imposing the reporting cost when disabled.


---

7. Correct design for multiple-loop fusion

7.1 Implement two distinct fusion layers

Layer A: CollectionPlan/pipeline fusion

Start here. It is safer and gives the largest intermediate-allocation wins.

source
  -> map(pure f)
  -> filter(pure predicate)
  -> take(k)
  -> reduce(...)

Lower to a single plan before materializing arrays. Advantages:

Cardinalities and ordering are explicit.

Intermediate ownership is known.

Callback effects can be checked at HIR level.

Exact reserve bounds can be derived.

Backend can choose scalar, SIMD, GPU, or parallel execution.


Futhark demonstrates aggressive fusion of high-level array operations, while stream-fusion research shows how producer and consumer representations can eliminate intermediate structures.

Layer B: General adjacent MIR loop fusion

Only after shared loop, dependence, and memory analyses are available.

Legality requirement
Simple proof

Real natural loops
Shared LoopForest, not block-order heuristics
Adjacent or control-equivalent execution
Dominance/post-dominance and no intervening effectful region
Compatible direction and trip count
SCEV-lite start, step, bound, signedness, no-wrap
No illegal cross-iteration dependence
Def-use plus MemorySSA-lite dependence direction/distance
Alias safety
Unique ownership, disjoint regions, imported noalias, or optional runtime versioning
Effect-order safety
No observable I/O, waits, atomics, volatile/device access, suspension, or exceptions whose ordering changes
Early exit compatibility
Equivalent break, continue, return, and exceptional behavior
Collection semantics
Order and uniqueness preserved
Numeric semantics
Preserve each reduction’s order unless fast-math explicitly allows reassociation
Profitability
Saved traversal/allocation versus register pressure, code size, vectorization, and cache behavior


LLVM’s LoopFusion pass requires canonical loop shape, compatible trip counts, control equivalence, and dependence legality. Its supporting SCEV, dependence, and memory analyses illustrate why loop fusion cannot be implemented as a short instruction-window rewrite.

7.2 Profitability model

Use a target-independent first model:

benefit =
    removed_loop_control
  + removed_loads_of_shared_input
  + removed_intermediate_bytes
  + improved_cache_reuse

cost =
    added_live_ranges
  + spill_risk
  + code_growth
  + lost_independent_vectorization
  + changed prefetch behavior

Then add target information:

SIMD width and register count,

cache-line and cache-size estimates,

branch cost,

element size,

expected trip count or profile,

GPU occupancy/register pressure.


Do not warn merely because the compiler declines fusion. Emit a structured missed remark:

remark[LOOP001/missed]:
  loops scan the same 8-byte element domain
  fusion rejected: output write in loop 1 may alias input read in loop 2
  required proof: disjoint regions or verified noalias contract


---

8. Research and production-language lessons

Source
What it demonstrates
Direct lesson for Simple

LLVM LoopFusion, SCEV, DependenceAnalysis
Fusion requires normalized loops, compatible trip counts, and dependence legality
Build reusable loop and dependence facts before a general fusion transform.
LLVM MemorySSA
Efficient representation and querying of memory definitions, uses, and clobbers
Replace repeated whole-function alias/memory scans with MemorySSA-lite.
LLVM/MLIR optimization remarks
Passed, missed, and analysis diagnostics can be structured and profile-aware
Performance opportunities should often be remarks, not source warnings.
Clang-tidy
Low-cost source checks detect reserve opportunities and avoidable copies
Implement exact local lints in Tier 0 with safe fix-its.
Rust Clippy
Detects unnecessary materialization and oversized stack usage
Type/layout-aware source linting is valuable without requiring optimizer proofs.
Go compiler and pprof
Escape decisions are explainable; allocations can be profiled by objects and bytes
Every failed stack promotion should explain its escape path and connect to profile data.
Futhark and stream fusion
High-level producer-consumer representations support systematic elimination of intermediate arrays
Build CollectionPlan fusion before arbitrary MIR loop fusion.
Infer Cost
Compositional symbolic cost summaries can identify algorithmic complexity across calls
Add cached function-level cost summaries for Robust/CI analysis.
SPEED and Loopus
Loop bounds and symbolic complexity can be inferred with bounded static analyses
Use a deliberately limited SCEV/cost domain rather than attempting unrestricted theorem proving in editor mode.
RaML/AARA
Amortized analysis can infer time and space/resource bounds
Represent amortized collection growth and bounded memory separately from worst-case per-operation cost.
Real-world performance-bug studies and Toddler
Repetitive computation and repetitive memory access are major dynamic bug signatures
Add a Tier-3 detector for repeated address/value patterns that static analysis cannot prove.



---

9. Implementation plan

Phase 0 — Make optimizer status truthful

1. Add PassStatus and PassExpectation.


2. Remove Skeleton and Disabled passes from effective pipelines.


3. Add --emit-opt-report=sdn|json|text:



PassRunRecord
    pass
    status
    functions_seen
    candidates
    transformed
    instructions_before
    instructions_after
    elapsed
    missed_reasons

4. Add one canonical positive sentinel for every MayTransform pass.


5. Fail CI when an active transform never changes its sentinel.


6. Add compiler self-lints for identity dispatch wrappers and empty module loops.


7. Display the effective pipeline, not merely the requested pass names.



This immediately distinguishes “not profitable on this program” from “the pass was never operational.”

Phase 1 — Shared linear-time analysis foundation

Implement and cache:

CFG successors and predecessors,

reverse-postorder,

dominator and post-dominator trees,

loop forest with real preheaders and latches,

linear def-use lists,

SCEV-lite,

region alias facts,

MemorySSA-lite,

quantitative effect summaries.


Replace:

string expression keys with structural keys,

worklist array slicing with an index or deque,

repeated array.contains sets with bitsets/dictionaries,

pass-local loop detection with shared LoopForest.


Add pass invalidation declarations:

preserves: [Cfg, Dominators, LoopForest]
invalidates: [DefUse, MemorySSA, Cost]

Phase 2 — Fast lints with immediate value

Implement first:

1. COLL009 nested dynamic iteration.


2. COLL010 linear lookup in loop.


3. COLL011 repeated materialization.


4. COLL012 sequential indexing.


5. COLL013 repeated sort/setup.


6. COLL014 unbounded flat-map.


7. COLL015 accidental Cartesian product.


8. COLL016 missing index.


9. MEM001 allocation in loop.


10. MEM002 missing reserve.


11. MEM004 needless materialization.


12. MEM005–007 avoidable large copies.


13. LOOP022 I/O/RPC/DB effect in loop.


14. LOOP023 wait/lock effect in loop.



All should consume the existing typed-HIR session and operation registry. No additional parse.

Phase 3 — Rehabilitate safe scalar transformations

Suggested activation order:

Order
Transform
Gate

1
Constant folding
Exact overflow, checked-op, FP, trap, and target-width semantics
2
Copy propagation
Complete def-use and mutation invalidation
3
DCE
Backward liveness/dataflow, side-effect and trap model
4
Local CSE
Structural keys, memory invalidation, no trapping-expression removal
5
True LICM
Real preheader, speculatability, MemorySSA and dominance
6
Exact reserve insertion
Exact/upper trip count and collection-growth contract
7
Bounds-check elimination
Dominance-scoped range proof and mutation invalidation
8
Stack promotion
Complete escape proof, size threshold, lifetime verification
9
TCO
Parallel parameter assignment and exception/debug semantics
10
GVN
Real dominator traversal and memory versioning


Every activation requires:

positive and negative MIR fixtures,

semantic differential execution before and after,

idempotence,

malformed/irreducible CFG tests,

overflow, exception, zero-trip, alias, and unsafe-pointer adversarial cases,

target/backend matrix tests,

optimization statistics proving the pass actually ran.


Phase 4 — CollectionPlan and loop fusion

1. Lower high-level collection pipelines to CollectionPlan.


2. Add effect, cardinality, ownership, and materialization nodes.


3. Eliminate dead intermediates.


4. Fuse pure producers and consumers.


5. Add multiple-reduction fusion.


6. Add adjacent MIR fusion only after dependence infrastructure is stable.


7. Add optional runtime alias versioning only under Aggressive/PGO profiles.



Phase 5 — Interprocedural and profile-guided analysis

1. Function CostSummary cached by semantic fingerprint.


2. SCC fixed point for recursive call graphs.


3. Baseline cost-diff CI:

new size variable,

increased polynomial degree,

increased allocation multiplicity,

new unbounded cardinality,

new I/O/wait effect under a dynamic loop.



4. Allocation profiles:

count,

total bytes,

peak live bytes,

survival/lifetime histogram.



5. Dynamic repetitive-access detector modeled after Toddler-style signatures.


6. Feed hotness into optimization remarks and layout recommendations.




---

10. Diagnostic format

Diagnostics should show the model and uncertainty rather than claiming an unsupported speedup.

Repeated lookup

warning[COLL010]: repeated linear lookup inside a dynamic loop
  outer iterations: orders.len
  lookup cost: users.len
  estimated work class: O(orders.len * users.len)

  users is not mutated in the loop.
  candidate: build Dict<UserId, User> once before the loop
  candidate work: O(users.len + orders.len)
  additional memory: O(users.len)

  no automatic rewrite:
    hashing, equality, iteration order, and memory behavior may change

Allocation multiplicity

warning[MEM001]: allocation occurs once per loop iteration
  allocation site: FormatBuffer
  multiplicity: records.len
  estimated allocations: O(records.len)

  candidate:
    reuse one buffer and clear it after each output

Missed fusion

remark[LOOP001/missed]: adjacent loops traverse the same domain
  trip count: data.len
  saved traversal if fused: one sequential pass
  fusion rejected:
    loop 1 writes region R3
    loop 2 reads region Unknown
  required proof:
    R3 is disjoint from loop 2 input, or a verified noalias contract

Escape reason

remark[MEM014]: allocation remains on the heap
  allocation size: 128 bytes
  multiplicity: items.len
  escape path:
    local tmp
      -> argument 2 of unknown external call
      -> may be retained

  stack promotion requires a verified noescape argument contract

Complexity regression

error[COLL017]: algorithmic cost increased against baseline
  baseline: O(items.len)
  current:  O(items.len * rules.len)

  introduced operation:
    rules.find(...) inside loop over items

  profile: Robust
  policy: reject new multiplicative input dimension


---

Final priority order

Priority
Work

P0
Make pass status truthful; add optimizer self-lints and effective-pipeline telemetry
P0
Keep BCE, vector rewriting, stack promotion, GVN, general LICM, string-builder rewriting, and TCO disabled until their correctness blockers are fixed
P0
Audit the active collection “hoisting” path for true preheader placement, zero-trip behavior, trapping operations, and effect safety
P1
Build shared CFG, dominators, loop forest, def-use, SCEV-lite, and MemorySSA-lite
P1
Run performance lints from cached typed-HIR/MIR artifacts; remove the separate parse bottleneck
P1
Implement COLL009–016, allocation-in-loop, reserve, needless materialization, repeated setup, and effect-in-loop rules
P2
Rehabilitate scalar transformations one at a time with semantic differential gates
P2
Implement CollectionPlan producer-consumer fusion and multiple-reduction fusion
P3
Add bounded interprocedural cost summaries and baseline complexity regression CI
P3
Add PGO allocation-lifetime, repetitive-access, false-sharing, and layout analysis


The central design principle is:

> The compiler should automatically transform only when equivalence, lifetime, aliasing, effects, and profitability are proved. The lint should expose likely algorithmic or representation mistakes when the better choice depends on application semantics. Optimization remarks should explain every important missed opportunity without turning normal source code into warning noise.

---

## Codex validation addendum — 2026-08-22

<!-- codex-research -->

This addendum validates the supplied audit against commit `37bd406e219cc35cae049b4130f5167c21801864`. Six parallel static lanes covered optimizer dispatch, lint diagnostics, shared MIR/escape facts, compiler/tool hot paths, existing tests/docs, and primary-source domain precedents. No compiler, test, or benchmark was executed during research. Detailed evidence is retained under `.spipe/simple_compiler_performance_memory_efficiency/research_lanes/`.

### Confirmed findings

- Thirteen registered pass entries have canonical identity or empty dispatch routes. `MirPassDescriptor` has typed kind/scope/cost metadata but no operational status or transform expectation, while current statistics count invocation names rather than candidates, transformations, instruction deltas, elapsed time, or missed reasons.
- Active collection “hoisting” inserts at the loop header rather than a verified preheader. This can remain per-iteration work; moving it outside the loop later requires explicit zero-trip, trap, and effect proofs.
- GVN substitutes block storage order for dominance; BCE pre-seeds loop proofs across all blocks; TCO assigns recursive arguments sequentially; DCE performs repeated local scans and conservatively retains the no-local-use case.
- Lint reparses source through `parse_module_silent_checked`. Existing repository measurements attribute about 99% of size-dependent lint time to this parse path. The measured scaling is approximately linear with a severe constant, not proven superlinear growth.
- Collection diagnostics are not present in the central lint-name/config mapping, so individual `COLL*` rules are not structurally configurable or suppressible. Core lint severity has no remark/info kind; SIMD emits ad-hoc `info`. JSON omits category, fixes, confidence, symbolic cost, evidence, and missed reasons.
- CFG, predecessors, loops, def-use, ranges, and alias approximations are independently rebuilt by multiple MIR passes with incompatible semantics. A revision-bound shared fact owner and explicit invalidation are prerequisites for safe activation.
- Escape finalization converts unresolved `Unknown` sites to `NoEscape`; production return terminator integration is a stub; size/alignment/frame thresholds and proof provenance are absent. Stack promotion must remain disabled.

### Corrections and refinements

1. Auto-vectorization is not purely `AnalysisOnly`. Canonical module dispatch performs a narrow elementwise MIR rewrite. Its step matcher accepts constants in `0..4` rather than proving exact step one and operand identity, making the issue an active correctness exposure. The unsafe rewrite must fail closed or be disabled before broader optimizer work.
2. Escape store/load methods use the same tuple-key form, but the production analyzer supplies inconsistent key inputs: a base-local value on store versus `0` on load. The audit conclusion remains valid, but the defect is at the integration boundary rather than the methods' tuple construction.
3. Single-file lint does not recursively scan the repository. Directory targets perform discovery; dictionary-based deduplication is already a fixed regression guard. Cold audit-script `find` calls should not be labeled hot-path defects without measurement.
4. CollectionPlan remains a research design rather than a production IR. Existing reserved `COLL009–018` identities align with the proposed rules, but implementing them safely requires typed operation, effect, cardinality, boundedness, and mutation facts rather than more string-pattern matching.

### Primary synthesis

The implementation order should be: immediately contain the active unsafe vector rewrite and active collection header-hoist behavior; make pass activation and effective pipelines truthful; unify structured diagnostic identities and parse/HIR reuse; land cached CFG/dominance/loop/def-use facts; make escape fail closed; add bounded Tier-0/1 diagnostics; then rehabilitate scalar transforms one at a time. MemorySSA-lite, CollectionPlan fusion, general loop fusion, bounded interprocedural cost analysis, and profile-guided layout work follow only after their proof inputs exist.
## 2026-08-22 implementation addendum: SSA dominance boundary

The checked optimizer boundary now extends its admitted proof surface beyond identity,
CFG closure, operand membership, and ABI locals. It builds shared CFG, def-use, and
immediate-dominator facts without liveness matrices and rejects undefined values,
multiple definitions, same-block use-before-definition, non-dominating cross-block uses,
and unavailable dominance. Call-terminator results are modeled on the normal edge so an
unwind path cannot falsely authorize their use. Stable codes `MIRV020` through `MIRV024`
identify these failures.

The verifier projection costs O(B + I + A + L) indexed storage plus bounded dominator
construction. It omits O(B*L) liveness matrices and definitions-by-uses Cartesian scans.
Normal builds construct none of these facts because checked dispatch remains behind the
cached verify-each gate. Opcode typing, ownership, and loop proof remain open.

## 2026-08-22 implementation addendum: partial opcode typing

The same structural instruction traversal now proves three exact local type contracts:
`Const` destination versus its explicit MIR type, `Copy`/`Move` source versus destination,
and `Cast`/`Bitcast` destination versus target. Stable `MIRV025`-`MIRV027` codes report
violations. Function and module receipts separately count type-checked and type-unchecked
instructions, preventing this subset from being mistaken for complete MIR typing.

Declared types are indexed once by local ID and compared structurally as `MirTypeKind`;
the verifier performs no per-check serialization and no second instruction scan. All
remaining opcodes are counted as unproved. Ownership and loop-boundary proof remain open.

## 2026-08-22 implementation addendum: lint-name membership

Collection diagnostics are already mapped to the stable `collection_performance` policy
owner and honor configuration/file-attribute suppression on this branch. The adjacent
configuration hot path still called `all_lint_names().contains(...)` once per SDN entry
and once per authored `@allow`/`@warn`/`@deny` name. Each call rebuilt the full name array
and then scanned it linearly.

`lint_name_is_known` now provides exhaustive allocation-free match dispatch. For K
authored names and N registered names, membership changes from O(K*N) comparisons plus K
temporary N-element arrays to O(K) dispatch and no membership allocation. Enumeration
remains available for `--warn-all`; a parity fixture checks every enumerated name against
the matcher and rejects recurrence of `all_lint_names().contains`.

## 2026-08-22 implementation addendum: effective lint defaults

`LintConfig.get_level` rebuilt `build_default_levels()` for every diagnostic without an
explicit override. With a selected profile it then built the tier projection as well.
Collection diagnostics commonly call policy twice—once for suppression and once for
effective severity—so a file with D diagnostics and N configured rules incurred O(D*N)
dictionary insertion/copy work and transient allocations unrelated to analysis.

`LintConfig.effective_defaults` now owns the immutable selected default table. It is built
once for a new configuration, recomputed only when the profile changes, and shared into
child configurations. `get_level` performs O(1) override/default lookups and allocates
nothing. Explicit overrides, profile semantics, evidence-tier capping, and suppression
behavior are unchanged. Project SDN discovery/caching remains a separate open tool lane.

## 2026-08-22 implementation addendum: request-local lint policy reuse

The standalone path loaded target `simple.sdn`, `lint_source` discovered and parsed it
again, and parsed AST rule append resolved it a third time. This multiplied parent-path
probes, file reads, source splitting, default/profile construction, and override copying
for the same file revision.

Parsed `LintConfig` now carries its exact `source_path`. Resolution reuses an already
loaded base policy when the discovered path matches. `Linter` also retains the exact
resolved config for only its immediately processed path, and parsed-rule append consumes
that value rather than resolving again. The retained state is overwritten on the next
file, so invalidation is request-local and no process-global stale policy cache exists.
Normal single-file CLI work reads/parses the target policy once instead of up to three
times. Directory-to-policy discovery caching remains open.

## 2026-08-22 implementation addendum: one-pass diagnostic policy

Central lint filtering and parsed AST append called `should_keep_lint_result` and then
`apply_config_level(_for_evidence)` for each retained diagnostic. Both independently
mapped the lint code and fetched its configured level. With D diagnostics, this doubled
policy dispatch and dictionary lookups after analysis had already completed.

`LintPolicyDecision` now returns `(keep, level)` from one code mapping and one effective
level lookup. The central source-lint result filter and all parsed append producers use
it. Unknown codes retain their authored level, explicit `allow` suppresses, warn promotes
allow-default rules, deny promotes proven findings, and unproved performance findings
remain warning-capped. The decision allocates no arrays/dictionaries and reads no source.
Compatibility wrappers remain for external callers pending staged migration.
