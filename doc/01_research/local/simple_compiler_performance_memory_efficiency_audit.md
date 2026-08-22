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

## 2026-08-22 implementation addendum: shared lint source view

The combined lint path split identical source into a line array in `lint_source` and then
again in parsed AST append. Besides a second O(source bytes) traversal, both arrays and
their line headers could overlap while the source-location index was constructed.

`lint_source_for_parsed_append` now explicitly opts into retaining the first line view.
Parsed append consumes that COW-owned array and calls `release_combined_lint_view` after
success. Non-Simple input, parse failure, and stale parsed-revision exits also release it.
Ordinary `lint_source` retains no view or resolved config. The combined path therefore
performs one split and keeps at most one source line view pending; long-lived linters do
not retain prior file contents after append. Exact AST spans remain the preferred future
replacement for fallback source-location indexing.

## 2026-08-22 implementation addendum: line-view consumers

After the combined-path fix, normal `lint_source` still caused independent line arrays in
file-attribute resolution and several line-oriented rule owners. These were semantic
readers of the same immutable source, not owners requiring separate storage.

The canonical `lines` view now feeds attribute resolution, parameter tags, raw-runtime
fix positioning, stale Markdown diagrams, LLVM type-safety guards, accessor/parent-name
analysis, freestanding patterns, and opt-in WM boundaries. Compatibility wrappers retain
string entrypoints for external callers, while normal lint uses `*_lines` variants. This
removes up to eight additional O(source bytes) splits/line-header arrays per applicable
file without changing iteration order or text matching. EasyFix registry owners still
contain independent splits and remain the next shared-view migration boundary.

## 2026-08-22 implementation addendum: quality-check line view

Five additional normal-path rule owners independently split the complete source:
feature-tracking traceability, SPipe quality, and the three raw typed-UI checks. Their
predicates and locations are exclusively line-based. They now accept the canonical
request line view directly, removing five O(source bytes) traversals and five transient
line-header arrays on applicable files. No whole-text predicate or diagnostic order
changed. EasyFix registry owners remain the next allocation boundary.

## 2026-08-22 implementation addendum: single EasyFix ownership

The normal lint path invoked the compiler EasyFix registry and then separately invoked
`primitive_api` and `simple_script_required`, although both are already registry members.
Applicable source was therefore scanned twice for each rule and identical fixes could be
appended twice. The redundant imports and append loops are removed. The registry is now
the single owner, cutting those rules from two executions to one and preventing duplicate
diagnostic/fix storage. Registry-wide shared line/context construction remains open.

## 2026-08-22 implementation addendum: shared SPipe EasyFix facts

The five SPipe EasyFix members are dispatched together, but four independently built a
full `LineContext` array and the missing-docstring rule built another line array. The
registry now accepts the lint request's canonical lines, builds one context array only for
`_spec.spl` files, and shares it across the four context rules; the fifth consumes the
same lines directly. Compatibility entrypoints keep their early file gate and construct
private facts only for standalone callers. Normal spec lint therefore removes one line
split plus three duplicate context arrays and their repeated trim/indent/offset work.

## 2026-08-22 implementation addendum: shared general EasyFix facts

The same `LineContext` derivation was repeated by resource-leak, struct-construction,
unknown decorator/attribute, export-boundary, and import-boundary rules. The registry now
builds one general request-owned context view and shares it with those rules and the SPipe
family. Non-exhaustive match and bypass checks consume canonical lines directly. The
duplicate-typed-argument rule also reuses both views, eliminating a fresh line array for
every candidate signature while retaining its existing candidate-by-line matching order.
Normal lint removes eight additional context/line arrays plus candidate-count-dependent
line arrays; the remaining repeated candidate traversal is tracked for a future indexed
call-site fact rather than being misreported as solved.

## 2026-08-22 implementation addendum: remaining compiler EasyFix lines

Six compiler-owned registry members still split the same source: star-import, wide-public,
bare-bool, primitive-API, short-grammar, and script-language checks. They now consume the
canonical line or context view. Primitive file-scope suppression also reads those lines,
avoiding a hidden second split. Compatibility wrappers preserve pre-split path gates for
facade and non-script files. Normal lint removes six line arrays plus the primitive allow
array and redundant short-grammar context derivation. Stdlib-owned contextual-keyword,
deprecated-if-let, and stub scanners remain the next cross-module view boundary.

## 2026-08-22 implementation addendum: canonical EasyFix context owner

The remaining contextual-keyword, deprecated-if-let, and stub rules lived in the stdlib
EasyFix layer and each built its own stdlib `LineContext` array. Worse, compiler EasyFix
helpers defined a structurally duplicate context type, preventing direct sharing. The
stdlib now owns `EasyFixSourceView(lines, contexts)` and view-taking rule entrypoints.
Compiler helpers re-export that canonical context type/builders instead of redefining
them, and the registry derives both compiler and stdlib rule facts from one view. Normal
lint therefore falls from four context arrays (one compiler plus three stdlib) to one,
with no additional split and no retained source after dispatch.

## 2026-08-22 implementation addendum: indexed duplicate-typed calls

Duplicate-typed-argument analysis still scanned every source line for every eligible
signature, giving O(signatures × source characters) matching after the array-allocation
fix. It now counts `(name, arity)` targets once, rejects ambiguous keys, tokenizes source
lines once, parses arguments only for eligible names, and records replacements by stable
signature index. Records are ordered by `(signature index, source sequence)` so fix and
replacement order remains unchanged. Cost becomes O(source characters + signatures +
replacements log replacements), with O(signatures + replacements) transient memory and
no per-signature source traversal or replacement-bucket COW growth.

## 2026-08-22 implementation addendum: allocation-free annotation and ID policy

Unknown-annotation checks reconstructed 31-entry decorator and 15-entry attribute arrays
for every annotation line, then linearly searched them. Exact match dispatch now encodes
the same sets without registry arrays or per-line allocation.

The lint bridge also parsed every EasyFix ID with `split(":")[1]`. Besides allocating a
parts array per fix, this misclassified direct IDs such as `W0406:17` as code `17`, so
suppression and severity policy targeted the wrong key. `lint_rule_code_from_easyfix_id`
now recognizes `L:`/`E:` namespaced IDs, preserves direct codes before the first colon,
and returns malformed IDs unchanged. It performs one necessary code slice and no parts
array, restoring correct W0404/W0406 policy ownership.

## 2026-08-22 implementation addendum: EasyFix policy reachability

Correct ID decoding exposed that many EasyFix codes already declared in
`all_lint_names()` and `build_default_levels()` still lacked a mapping to those names.
Rules including export boundaries, SPipe quality, resource leaks, annotation validity,
and stub detection therefore ignored authored suppression and configured/default deny
levels. Exact allocation-free mapping now covers every existing configurable EasyFix
name, while W0406 maps to `visibility_boundary` alongside W0401–W0404. Default-deny
`export_outside_init` now promotes to deny, and an explicit allow suppresses it through
the same one-pass `LintPolicyDecision` used by other diagnostics.

## 2026-08-22 implementation addendum: advisory EasyFix policy completeness

Six emitted EasyFix families had no configurable identity: contextual-keyword ordering,
deprecated `if let`, struct-construction parentheses, four short-grammar variants,
raw-unit postfix, and SIMD opportunity. They are now registered with warning defaults and
allocation-free membership. Exact emitted-code mapping routes the four short-grammar IDs
to one `short_grammar_refactor` policy and maps the other codes directly. Users and CI can
now allow, warn, or deny every emitted EasyFix family rather than relying on an immutable
authored warning level.

## 2026-08-22 implementation addendum: honest unknown-annotation fallback

The source scanner ran `unknown_decorator` and `unknown_attribute` over the same `@name`
syntax using disjoint allowlists. Known decorators such as `@extern` could therefore be
reported as unknown attributes, known attributes could be reported as decorators, and a
truly unknown name produced two warnings and two fix objects. Raw source has no fact that
can distinguish those categories.

Normal registry dispatch now runs one `unknown_annotation` fallback against the union of
both known sets and emits at most one advisory per line. Legacy standalone functions
remain for compatibility. `unknown_annotation` is a real configurable name; setting it
updates both legacy aliases, while setting either legacy name updates the generic owner.
Typed HIR remains the future owner for decorator-versus-attribute classification. Normal
cost falls from two full context scans to one and duplicate diagnostic/fix storage is
removed.

## 2026-08-22 implementation addendum: remove unsafe hoist bodies

Collection hoisting was already fail-closed at both public compatibility entrypoints, but
each unconditional return was followed by a complete unreachable header-insertion
implementation and private legality helpers. Those bodies parsed and compiled despite
never executing, duplicated roughly 190 lines, and made accidental resurrection of the
known zero-trip/preheader defect a one-line edit.

Both unreachable transforms and their private-only helpers are removed. The inert
entrypoints remain and return the original blocks. Scalar-invariance predicates retained
as analysis scaffolding do not move MIR. Re-enabling collection LICM now requires a new
implementation built on a real preheader, dominance, MemorySSA/alias/effect facts, and
non-trapping speculatability rather than uncommenting unsafe header insertion. This
reduces compiler source/IR size and closes a correctness footgun without claiming LICM.
## 2026-08-22 follow-up: dormant trip-count recognizer removal

The shared loop detector correctly returns an unknown trip count until SCEV-lite can prove initialization, signed step, direction, branch polarity, nowrap behavior, and finiteness. It nevertheless retained an unreachable comparison-bound recognizer after that return. The recognizer confused a loop bound with an exact iteration count and could be activated mechanically without the missing proofs. The unreachable body and its two private-only parsing helpers were removed. This reduces compiler source/parse memory and prevents unsafe strength-reduction, unrolling, vectorization, or reserve decisions from acquiring a plausible-looking but invalid trip count.
## 2026-08-22 follow-up: dormant TCO rewrite removal

Tail-call optimization remains structurally `Skeleton`, and canonical dispatch returns the original function. The file nevertheless retained a private rewrite that copied recursive-call arguments directly into parameter locals in sequence. For `f(a, b) -> f(b, a)`, the first assignment can destroy the value needed by the second; arity, type, ownership/destruction, effect, unwind, and debug contracts were also absent. The dormant implementation was removed while the factory, class, statistics, and identity entrypoints remain compatible. Rehabilitation requires parallel temporaries plus semantic differential witnesses. Removing the body also lowers compiler parse/compile work and dead IR memory.

The parallel lint audit also identified the next dominant tooling target: repository lint constructs the rule registry, discovers/parses project policy, and reads critical-mode configuration per file. A CLI-scoped `LintSession` should own the immutable registry and bounded config caches, and each source should be read once even when SIMD checks are requested.
## 2026-08-22 implementation follow-up: command-scoped lint registry reuse

Repository lint now constructs one `Linter` before its file loop and passes it through `run_lint_file_with_linter`. This removes file-count-multiplied construction of the roughly 56 immutable rule descriptors. A bounded last-project cache reuses the parsed `simple.sdn` configuration for adjacent files in the same discovered project and clones it before applying per-file/CLI policy, avoiding shared mutation and process-global stale state. Standalone `run_lint_file` remains a one-file compatibility wrapper. Remaining work is to cache directory-to-manifest discovery, load critical-mode policy once, and share the single source read with optional SIMD and fix application.
## 2026-08-22 implementation follow-up: one lint/SIMD source payload

The repository CLI now reads each validated source through the error-aware lint reader once, passes that exact payload to the command-scoped linter, and reuses it for optional SIMD opportunity analysis. A valid empty file remains distinct from a read failure. Standalone `run_lint_file` and `run_lint_file_with_linter` retain their file-reading compatibility behavior, while `run_lint_source_with_linter` exposes source ownership for batch tools. Fix application still rereads immediately before writing so it does not apply replacements to an unvalidated stale payload.
## 2026-08-22 implementation follow-up: critical policy session snapshot

`check_dynamic_capability_acquire_spl` formerly loaded and parsed `config/critical_mode.sdn` once per source file, including the common disabled case that emits no finding. The command-owned `Linter` now lazily resolves only the effective dynamic-acquire mode on first use and reuses that scalar for the batch. This removes file-count-multiplied filesystem probes, source allocation, line splitting, and configuration-object allocation. The cache is scoped to one lint command, so it cannot become stale across long-lived daemon requests.
## 2026-08-22 implementation follow-up: bounded manifest discovery cache

Per-file lint previously walked up to ten ancestors to discover `simple.sdn`, then `lint_source` repeated discovery while resolving file attributes. The command-owned `Linter` now caches directory-to-manifest outcomes, including misses, checks cached ancestors during traversal, and caps retained directory entries at 4096. A prepared-path marker tells `lint_source` that manifest resolution is already complete, so it only clones base policy and applies file attributes. This removes the second walk entirely and shares common-ancestor results across sibling directories while bounding batch memory.
## 2026-08-22 implementation follow-up: bounded parsed-policy cache

The first command-session stage cached only the most recently parsed `simple.sdn`; alternating files from multiple projects could still reparse the same manifests repeatedly. The `Linter` now indexes up to 256 unique manifest paths into flat `LintConfig` storage. Hits clone the stored configuration before applying CLI or file-local overrides. The flat index avoids struct-valued dictionary retrieval hazards; after saturation, new manifests are parsed without retention, preserving correctness with bounded memory.
## 2026-08-22 implementation follow-up: shared manifest-free defaults

Sources without a discovered `simple.sdn` still constructed `LintConfig.new()` per file, rebuilding the complete effective-default dictionary even though defaults are immutable. `Linter.new` now creates one manifest-free base policy for the command. Each file receives `child()`, which allocates only its mutable overrides while sharing the immutable defaults. Direct caller configuration remains separate, and profile changes replace the child's defaults rather than mutating the cached base.
## 2026-08-22 implementation follow-up: storage-layout advisory indexing

The active storage-layout advisory deduplicated field IDs by scanning a growing array and deterministically ordered textual identity rows with a handwritten selection sort. Both were quadratic in typed access facts, in addition to the separate semantic overlap check. Field membership is now dictionary-indexed with an explicit count, eliminating the ID array and its repeated scans; identity rows use the standard deterministic sort, reducing ordering from `O(F²)` comparisons to the library sort complexity. The semantic overlap pair analysis remains unchanged and fail-closed pending a region-grouped interval-sweep design.
## 2026-08-22 follow-up: incomplete string-builder rewrite removal

String-builder optimization is structurally `Skeleton` and canonical dispatch is an identity, but its class retained an unreachable transform. The body allocated only a numeric local ID and replaced concatenation with a `push` call; it never declared or initialized the parts collection and never emitted the final join/result assignment promised by its comments. The private candidate/rewrite machinery and unused loop detector state were removed while factory, statistics, class, and identity entrypoints remain. This prevents mechanical activation of malformed MIR and removes dead parse/compile and pass-construction memory.
## 2026-08-22 follow-up: strength-reduction bypass closure

Strength reduction is structurally `Disabled` and canonical dispatch returns the input, but its exported class and `reduce_block` method still allowed direct execution of dormant rewrites. Those rewrites included signed division/remainder by powers of two and fixed synthetic local IDs without enforcing the provider's non-negative/unsigned and width facts at each operation. The class is now a compatibility skeleton: function and block entrypoints are identities, provider proof metadata and zero statistics remain, and all rewrite helpers/local allocation are removed. Legacy tests now prove fail-closed behavior rather than bypassing dispatch to exercise unsafe transformations.
## 2026-08-22 follow-up: GVN block-order bypass removal

GVN is structurally `Skeleton` and its canonical wrapper is an identity, but the exported class still executed a dormant implementation directly. It chose expression leaders while iterating MIR storage order—explicitly described as an approximation of dominator order—and reused field loads without memory-version/alias invalidation. The value-number tables, text-signature allocation, block/instruction rewrites, and mask-identity side transform were removed. Class/factory/statistics compatibility remains identity, preventing non-dominating reuse and eliminating dead compiler allocation/hash work.
## 2026-08-22 follow-up: bounds-check removal bypass closure

Bounds-check elimination is structurally `Disabled`, but its exported class still removed checks when called directly. It globally collected local loop-shape records, converted them to textual keys, and pre-seeded every block’s seen-check set, so a proof was not scoped to a dominated loop region. Same-block deduplication also assumed stable operand versions. All recognition, textual key allocation, proof seeding, and removal bodies are gone. Public proof record types, counters, dependencies, factory, and identity block/function entrypoints remain compatible.
## 2026-08-22 follow-up: general loop-transform bypass closure

LICM and loop unrolling are structurally `Disabled`, yet their exported class methods still rewrote MIR directly, and `LoopOptimization.run_on_function` chained those methods without consulting canonical status. LICM synthesized a new block and redirected predecessors without complete preheader/dominance/effect/speculatability/zero-trip proof; unrolling duplicated instructions without induction substitution or complete control/effect handling. All rewrite bodies and loop-detector allocation were removed. Compatibility classes, counters, thresholds, factories, dependencies, and identity methods remain.
## 2026-08-22 follow-up: generator transform quarantine and analysis cost

Generator state-machine optimization is structurally `Skeleton`, but its exported class directly built a new signature, locals, dispatcher, state blocks, loads/stores, and returns. No other pure-Simple lowering path consumed this optimizer class, and the runtime still records pending generator support. The transform and private segment builder were removed; both class transform entrypoints are identities. Exported yield discovery remains analysis-only and now tracks definitions in one forward walk instead of rescanning the entire function for every yield. Conservative per-yield local snapshots remain `O(Y*L)` and cannot authorize frame layout.

### Body-outlining quarantine result

Body outlining is structurally `Skeleton`: canonical function dispatch returned the input and module dispatch iterated functions without processing them. The same file nevertheless retained directly callable cold-region grouping, live-variable collection, CFG extraction, exit remapping, synthetic function construction, and original-function rewriting. Its cold propagation could classify predecessors from successor coldness without dominance, frequency, or control-equivalence proof, while helper lookups repeatedly scanned blocks and locals and the rewrite cloned MIR arrays. The dormant rewrite and private helpers were removed. Exported compatibility classes, counters, factory, and function/module identity entrypoints remain. This closes the mechanical activation bypass and removes roughly 600 lines of dead compiler parsing, compilation, allocation, and instruction-cache footprint. Rehabilitation requires canonical CFG/loop facts, complete live-in/live-out and ownership analysis, verified symbol/ABI construction, unwind/debug equivalence, profitability evidence, and semantic differential witnesses.

### Local-CSE quarantine result

Local CSE is structurally `Skeleton`, and its canonical wrapper returned the input, but `CommonSubexprElimination.run_on_function` still rewrote MIR directly. The dormant implementation treated `Move` and `Copy` operands as interchangeable, treated `GetField` as pure, and invalidated its table only for direct `Store` and `Call`; `SetField`, globals, indirect/intrinsic calls, other effects, local redefinitions, traps, and ownership consumption were not modeled. It also formatted text keys on lookup and again on insertion, recreated dictionaries per block, and rebuilt every instruction/block/function array even without a match. Rewrite construction and leader-table mutation were removed while exported representation/table/class/factory/statistics compatibility remains fail-closed. This prevents direct unsafe reuse and removes dead compile-time hashing, allocation, cloning, and source footprint. Rehabilitation requires structural keys, exact Copy/Move semantics, definition kills, effect/trap facts, and MemorySSA-lite versions.

The parallel scalar-pass review also found that copy propagation never constructs its copy map, omits most MIR operand families, and conflates moves with copies; constant folding can attach the RHS integer type to a folded boolean comparison and lacks explicit overflow/division/shift legality; DCE pays dense liveness plus per-block/local scans and still needs a complete trap/effect contract. These remain Skeleton work. Copy propagation should be the first activation candidate only after exhaustive local Copy-only rewriting and witnesses; constant folding follows after shared evaluator semantics and result typing; DCE follows sparse-liveness and opcode observability review.

### Command-scoped lint policy result

Repository lint already owns one `Linter`, source payload, manifest-discovery cache, and parsed-policy cache per command, but it still passed the complete normalized CLI array—including every positional target—to every file. Each file performed six flag membership scans, another full profile scan plus slice/parse, and a WM-lane scan. For N explicitly listed files the argument-policy component was `O(N^2)` text comparisons; directory lint remained linear but repeated invariant parsing per file. `LintCliPolicy` now parses flags and the optional profile once, before the file loop, and the policy-aware source entrypoint reuses that command snapshot. Standalone args-based wrappers remain compatible by constructing one policy for their single invocation. Manifest policy → CLI profile → file-header precedence, deprecated-alias warn-once behavior, fix modes, and warning/error semantics are preserved. Retained command memory is constant-size policy state rather than per-file argument-derived temporaries.

### Copy-propagation quarantine result

Copy propagation is structurally `Skeleton` and its canonical function wrapper returned the input, but five callable helpers retained a partial rewrite. The pass never populated its copy map, covered only a small subset of operand-bearing MIR, treated consuming `Move` like `Copy`, followed chains up to an arbitrary 1024 steps per use without compression or explicit cycle failure, and rebuilt argument, instruction, block, and terminator arrays. Those helpers were removed while exported `CopyChain`, `CopyPropagation`, factory, fields, zero statistics, and identity wrapper remain compatible. The former tests did not invoke production code: they simulated an unrelated copy-to-move algorithm and falsely documented it as active. They and the generated manual now assert quarantine instead. This removes dead chain traversal and MIR allocation work plus roughly 230 lines of compiler source. Rehabilitation begins with block-local Copy-only propagation, exhaustive opcode coverage, dominance/redefinition kills, cycle-safe near-linear roots, exact receipts, and differential tests; Move remains excluded until ownership/destruction semantics are proved.

### Legacy optimization-engine function-state fix

The separate compatibility `OptimizationEngine` retained `const_map`, `type_map`, `def_map`, `use_count`, and `expr_map` across `optimize_function` calls. MIR builders restart local numbering at zero for every function, so an engine reused across functions could read a stale constant or defining instruction under the same `LocalId` and incorrectly fold or simplify the later function. It also retained `MirInst` graphs and dictionary high-water storage for the engine lifetime; increasing/sparse IDs could grow this monotonically. Every function entry now replaces all five maps before even the `None_` early return, while cumulative optimization statistics and the configured level remain intact. A regression seeds all maps, calls the no-optimization path, proves every entry is gone, and proves statistics persist. This is an active correctness and retained-memory fix, not merely Skeleton cleanup.

The parallel constant-fold review additionally found a semantic-layer `run_const_fold_pass` that allocates an evaluator, walks functions, discards every reconstructed body, and always returns the original module; the driver still invokes it. That no-op traversal is the next tooling/compiler hot-path removal. It is distinct from the canonical MIR constant-folding Skeleton and from semantic constant evaluation used by language features.

### Semantic HIR constant-fold no-op removal

The bootstrap HIR driver invoked `run_const_fold_pass` after method resolution. That pass allocated `ConstEvaluator`, iterated every function and selected statement/value expressions, constructed replacement statement/block arrays, incremented a fold count, but never wrote `updated_func` back to the module and always returned the original module. The driver import/call, semantic barrel export, and dead pass file were removed; resolved modules now enter validation directly. Repository search found no other users of the pass or its literal helpers. Separate `const_eval.spl` functionality remains available for language semantics, and the MIR constant-fold pass remains the canonical optimization owner in `Skeleton` status. Source contracts pin all three boundaries. This removes size-dependent compiler CPU and transient HIR/evaluator allocation without changing output semantics.

### Compact lint source-location retention

The combined text-lint/parsed-AST path retained the entire `content.split("\n")` array across parsing solely so parsed fallback diagnostics could later build function, collection-fix, and star-export line maps. It then held the line array and all three maps together through every AST diagnostic loop. For `.spl` sources, the text phase now builds the compact location maps while its canonical line view is already live, retains only those dictionaries plus resolved config/path, publishes validity after all maps, and releases all combined-view state immediately after the parsed append materializes config and the index. Non-Simple files do not build the handoff; defensive non-combined callers still split and index locally. Parse-failure and stale-revision paths pay the compact indexing scan before rejecting, trading bounded transient CPU for eliminating source-text retention across the parser. This removes source-sized line-text retention, avoids a second successful-path source scan, bounds retained material to diagnostic location keys, and shortens even that lifetime before AST result construction.

### MIR constant-folding quarantine result

Canonical MIR constant folding was correctly marked `Skeleton` and excluded from effective pipelines, but `ConstantFolding.run_on_function`, block/instruction/terminator methods, `ConstantEvaluator`, and `AlgebraicSimplifier` still transformed on direct calls. The evaluator erased integer widths and signedness into `i64`, used host arithmetic without explicit overflow, `MIN/-1`, division/remainder, or shift legality, and represented F32/F64 through `f64` without target rounding/NaN/signed-zero contracts. Comparison folds could attach the RHS integer type to a boolean result. Algebraic identities ignored type/trap differences, while every direct run rebuilt block/instruction/function arrays even unchanged. All callable surfaces now return their inputs or `nil`; compatibility classes, fields, factory, methods, and zero statistics remain. Misleading positive rewrite fixtures/manual were replaced with quarantine and requested-versus-effective pipeline contracts. This removes about 470 lines of dormant arithmetic/rewrite code and its direct-call allocation risk. Rehabilitation requires one shared typed evaluator, exact target/language semantics, no-change storage reuse, receipts, verification, idempotence, and differential execution.

### In-place lint result compaction

Each lint invocation accumulated diagnostics in `self.results`, then allocated and grew a second `filtered_results` array while both held the same file's retained messages, fixes, evidence, and uncertainty records. Filtering now uses stable indexed compaction directly on the request-owned field: `write <= read` guarantees no unread slot is overwritten, kept order is unchanged, severity changes still construct an isolated diagnostic/result, and tail entries are popped only after the original range is scanned. This removes the second result-array capacity and peak reference retention. It deliberately avoids aliasing the value-semantic array into a local mutable copy. Source contracts pin the indexed loop, direct field writes, tail truncation, and absence of the old buffer.

### Dead-code-elimination quarantine result

DCE was registered as a `Skeleton`, but `DeadCodeElimination.run_on_function`
still provided a direct transformation bypass. That body built dense shared
liveness, scanned block/local combinations, allocated live and keep tables plus
rebuilt instruction arrays, and deleted instructions using an incomplete
observability/trap contract. All transform surfaces are now identity and the
Skeleton path performs none of that work. The mandatory decision/condition
probe classifier remains analysis compatibility only; side-effect and intrinsic
purity queries fail closed. Rehabilitation requires exhaustive opcode effects,
traps, ownership/destruction, unwind, volatile/atomic/device and debug semantics,
plus sparse/worklist liveness with explicit CPU and memory budgets.

### Capability-scoped PerfFacts construction

Four active compiler analyses requested full `perf_facts_build` despite never
querying liveness: natural-loop detection, vectorization dependency analysis,
storage-access analysis, and typed-storage-view production. Below the existing
four-million-cell admission cap, each call could initialize DEF/USE and live-in/
live-out matrices proportional to `blocks * locals` and run repeated whole-local
liveness propagation. A new `perf_facts_build_without_liveness` projection keeps
CFG, dominance and def-use behavior while omitting all four matrices and the
worklist. The verifier name remains a compatibility alias. The next refinement
is an integrity-checked fact request so loop detection can omit def-use and
def-use-only consumers can omit dominance.

### Linear diagnostic evidence rendering

Human and JSON warning/error evidence used repeated immutable text append. For
a rendered payload of `B` bytes, cumulative copied bytes could grow quadratically
even though peak output is only `O(B)`. Both paths now collect complete logical
lines/items and join once, preserving exact ordering and escaping. Focused
contracts pin the human byte sequence and prohibit recurrence of append loops.

### Accessor field-rewrite hot-path indexing

The active `short_grammar_field_access` rule ignored the registry's canonical
line/context view, split the source again in both its checker and accessor parser,
allocated a redundant line-start array, called a linear same-suffix search for
every dummy method, and then compared every class line with every surviving
dummy. Accessor-heavy classes therefore approached `O(methods^2 + lines*methods)`
plus two extra source-sized line views. The registry now passes canonical lines
and byte offsets. Parsing accepts lines directly; each class indexes real fields
and unambiguous dummy names once; each line extracts only actual accessor-shaped
call names for dictionary lookup. The public source wrapper remains compatible
and performs one split for standalone callers. Conflicting mappings fail closed.

### Warning-path quadratic scan removals

The active `primitive_api` rule asked `line_is_allowed` to walk backward through
comments, blanks and annotations for every source line before checking whether
the line was a public function. A comment-only file therefore performed
`1 + ... + lines` suppression work while it could not emit a finding. Candidate
classification now occurs first; byte offsets advance once on rejected lines,
and suppression runs only for public-function candidates. Because declarations
bound their preceding annotation runs, total work is linear in source lines.

The `_spec.spl` minimal-docstring warning separately counted delimiters with
`source.slice(cursor).find`, repeatedly allocating and searching the remaining
suffix. It now uses absolute `index_of_from` cursor advancement, reducing worst-
case `O(N^2)` copied/scanned bytes to `O(N)` time and `O(1)` auxiliary memory.
Two byte-identical `check_silent_default_spl` method declarations were also
removed so the warning has one implementation owner.

### Dependency-closed PerfFacts requests

The no-liveness projection still built CFG, reverse postorder, dominators and
def-use for every consumer. Production needs are narrower: loop detection needs
CFG plus dominance; storage-access analysis needs def-use only; vector dependency
and typed-storage rewriting need CFG integrity plus def-use. `PerfFactRequest`
now exposes those capabilities with
closure rules (`dominators => cfg`, `liveness => cfg + def_use`) and diagnostics
for implicit expansion. Loop detection no longer classifies instructions or
allocates local buckets/def-use sites. Def-use clients no longer build edge maps,
DFS/RPO state or iterative dominators. Legacy full/no-liveness/verifier builders
retain compatibility. Unrequested families are empty and report incomplete, so
missing work cannot accidentally authorize a transformation.

Independent review caught two capability-integrity gaps before further work.
Dominance now has an explicit `dominators_complete` bit and loop detection exits
unless it is true. Vectorization and typed-storage rewriting use the CFG+def-use
preset and reject duplicate/missing block identities before interpreting sites
keyed by block ID. They still omit RPO/dominator and liveness work.

### Wide-public export deduplication

The canonical `wide_public` text rule retained every unique export name in an
array and called a private linear `list_has` for each parsed name. A module with
`E` distinct exports therefore performed `0 + ... + E-1` name comparisons.
The rule now uses a dictionary-backed membership set and an explicit scalar
count, avoiding unreliable dictionary-length behavior while reducing expected
CPU to linear in parsed export names. Exact textual identity, case sensitivity,
duplicate suppression, exclusions and diagnostic counts are unchanged; no name
iteration order is observable.

### Default diagnostic policy fast path

The query/LSP emitter previously extracted every diagnostic code from serialized
JSON before discovering that no severity override existed. Normal builds without
an explicit lint profile therefore paid a full diagnostic-text scan and allocated
a code substring per result. The emitter now consults an explicit override-entry
count first. The config loader owns the dictionary and count together, resets both
at request boundaries, and increments the count only when it inserts an Allow or
Deny override. This avoids relying on native dictionary length behavior and makes
the default path constant-time before its required emit/collect operation.

### Linear PerfFacts predecessor construction

Shared CFG construction previously read each predecessor array from a dictionary,
appended to the local value, then wrote it back for every edge. Under Simple's COW
value semantics, a join with indegree `D` could copy lists of sizes `0..D-1`, for
`O(D²)` CPU and transient copied elements; a graph can reach `O(E²)` in the worst
case. PerfFacts now assigns each successor ID one owned nested-array bucket,
appends edges there in MIR storage/terminator order, publishes each completed
list to the dictionary once, and releases builder-only indexes before later
analyses. Construction is expected `O(E + T)` time and
`O(E + T)` storage for `T` distinct targets. Duplicate edges, dangling targets,
duplicate source identities, and predecessor ordering remain unchanged.

### Linear short-lambda discovery

The short-grammar EasyFix rule recursively searched for each backslash and then
rescanned the entire preceding line twice to decide whether the candidate followed
a comment or appeared inside a quoted string. A line of length `N` containing
`K = O(N)` backslashes therefore took `O(N²)` character work and `O(K)` recursive
stack depth. The rule now scans the line once, stops at the same first `#`, keeps
the same simple quote-toggle state, and records only syntactically eligible
backslash positions. Candidate parsing and replacement ordering are unchanged.
Discovery is `O(N)` time with `O(K)` compact position storage and no recursive
stack-growth hazard. Candidate-specific functional-update and short-grammar
parsers initially retained their existing costs. Follow-up removed the largest
remaining candidate multiplier: the first non-function-type `->` boundary is now
classified once per line and compared with each lambda position in constant time,
rather than rescanning from byte zero for every candidate. Individual candidate
parsers retain their syntax-dependent costs, so this does not claim an
end-to-end linear rewrite rule for every adversarial expression shape.

### Fail-fast dense liveness storage

PerfFacts formerly allocated both dense live-in/live-out matrices before checking
whether CFG and def-use inputs were complete. It also retained dense per-block
USE/DEF matrices after liveness had failed closed. Invalid MIR could therefore
retain four `blocks * locals` boolean matrices despite authorizing no liveness
query. The liveness builder now rejects incomplete inputs before allocating its
two output matrices. Duplicate-local incompleteness prevents all four matrices;
later CFG/instruction incompleteness allocates only the USE/DEF working pair and
releases it before returning facts. Complete-input semantics and the four-million
cell budget are unchanged.

### Unchanged CLI diagnostic policy projection

The active lint CLI applied policy by reconstructing every `LintRunResult` and
`LintDiag`, even when the computed severity equaled the authored severity. That
is the entire normal `deny_all = false` path, every already-Deny/Allow diagnostic,
and unproven performance warnings that remain advisory under deny-all. The helper
now computes the effective level once and returns the immutable input result when
it is unchanged. Only a real Warn-to-Deny transition rebuilds the diagnostic.
Traversal remains `O(D)`, but unchanged diagnostics avoid constructor dispatch,
COW/reference traffic for message/fix/evidence/uncertainty payloads, and transient
result objects. Formatting, ordering, counts, and JSON/text bytes are unchanged.

### Linear natural-loop latch aggregation

`LoopDetector.detect_loops` formerly stored a growing latch array in a dictionary.
Every dominance-proven edge extracted that value, linearly scanned it for a
duplicate source, appended, and wrote it back. A header with `L` latch edges paid
`O(L²)` comparisons and, under COW value semantics, potentially `O(L²)` copied
elements/transient allocation. Loop detection now assigns each first-seen header
an owned latch bucket plus an indexed membership dictionary. Each backedge is
admitted once in expected constant time and appended directly. Total aggregation
is expected `O(E)`; header order and per-header latch order remain first CFG
traversal order, and repeated edges from one source/header still coalesce.

### Bounded fast path for applying source fixes

The active `FixToolApplicator` selection-sorted every file's replacements in
`O(R²)`, then rebuilt the complete source after each edit, copying roughly
`O(R * S)` bytes for small edits. The compatibility-safe path now uses a typed,
stable merge sort (`O(R log R)`) by descending start. Left-first equality retains
discovery order within an equal-start group. It validates
overlap exactly as before, and assembles untouched chunks plus replacement text
with one final join (`O(S + output)` copied bytes). Equal-start edits therefore
retain their historical insertion order without the former quadratic fallback.
Negative, reversed, or originally out-of-range spans retain incremental legacy
application because dynamic length checks are also observable. Missing-source and
overlap errors are unchanged. Follow-up replaced per-file dictionary array
copyback with stable integer bucket indexes and owned nested replacement arrays,
making grouping expected `O(R)` while retaining dictionary key iteration and
per-file discovery order. The ordering/assembly implementation now lives with
`std.tooling.easy_fix.types.FixApplicator`: compiler `FixToolApplicator`
delegates to it, and lint `--fix` calls the same exported primitives. This removes
the remaining selection-sort/repeated-splice copies and prevents behavioral
or performance drift among the three active entrypoints.

### Diagnostic JSON escaping allocation audit

The lint and compiler-diagnostic query paths each serialized every message with
five chained whole-text replacements. For a message of length `M`, this remained
`O(M)` but performed about five scans and could allocate/copy five complete
intermediates per diagnostic. Both paths now delegate to one Pure Simple helper.
It returns an unchanged value directly when no JSON escape is present; otherwise
it performs one character scan, records unchanged spans and exact escape literals,
then joins once. The accepted escape set remains exactly backslash, quote, LF, CR
and TAB; other text, including Unicode, is unchanged.

### ANSI-free diagnostic output allocation audit

`query check` normalizes combined compiler stdout/stderr before deciding whether
lint may run, and JSON/count paths normalize it again. `_strip_ansi` previously
pushed every retained character into a text array and joined it even when the
compiler emitted no ANSI escape—the normal machine-consumer case. This created
`O(M)` tiny fragments plus a full output copy per normalization. A preliminary
escape scan now returns the original text directly when ESC is absent, eliminating
that common-case auxiliary allocation. ANSI-bearing input still uses the original
state machine exactly: ESC begins suppression, lowercase `m` ends it, and an
unterminated sequence drops the remaining suffix. Sharing the already-normalized
combined output across the decision and JSON parser remains a larger internal API
follow-up.

### Workspace diagnostics repeated-startup audit

The active workspace command loops over discovered files and launches one
`simple check` child for each text result. JSON launches `simple run ... query
check` per file, and that child launches `simple check` again: `N` files therefore
cost `N` child processes in text mode and `2N` in JSON mode, plus repeated compiler
startup, configuration, frontend state and output parsing. The LSP/MCP tool already
documents nested-check deadlock risk and disables this path by default.

The safe replacement is not naive parallelism: parser, lexer, AST pools and lint
collection still contain module-global mutable state. Introduce a serial in-process
`WorkspaceDiagnosticSession` first. Freeze command configuration once, create a
fresh compilation/diagnostic context per file, pass source directly to lint, tag
results with discovery ordinals and preserve standalone per-file isolation. Move
parser-owned globals into request/session state before bounded workers are enabled.

### Variable-reassignment analysis map audit

The active SSA/JIT admission analysis represented counts, alias parents, borrowed
roots and escaped roots as parallel arrays. Each instruction/operand linearly
searched growing local sets; alias resolution repeated that search up to 64 times,
and unique insertions copied growing arrays under current value semantics. For `I`
visits and `L` locals this produced `O(I*L + L²)` work and quadratic cumulative
copied-element traffic.

The analyzer now uses local `Dict<i64,i64>` count/alias maps and
`Dict<i64,bool>` sets. Membership is always `contains_key` followed by a typed
bracket read; local ID 0 never passes through optional truthiness. Alias walking
retains its exact 64-transition bound and no path compression. Instruction order
is unchanged: check the destination against its old root, count the definition,
capture Ref borrows, capture escapes using old aliases, then install/reset the
new alias. Final count/escape aggregation is commutative, so dictionary key order
cannot affect public booleans, counts, reasons or fixed JIT fact order. Expected
runtime is `O(I*64 + L)` with `O(L)` retained state.

### Bare-import file reconstruction audit

The standalone Pure Simple bare-import fixer already scanned each line once, but
then reconstructed every changed file by appending `"\n" + line` to an immutable
growing prefix. A file with `S` output bytes across `L` lines could copy
`O(S*L)` bytes and reaches quadratic behavior for similar-length lines. The fixer
now joins the completed line array once, giving `O(S)` output assembly. Because
the same `split(content, "\n")` result is joined with the same delimiter, empty
interior lines and the trailing empty item that represents a final newline remain
unchanged. Atomic-write failure and unchanged/written status values are untouched.

### MCP diagnostic wrapper allocation audit

Both query-check implementations independently joined every serialized diagnostic
into a full array string, concatenated that payload into another full
`structuredContent` string, then joined a final envelope. Total work remained
linear in diagnostic bytes `S`, but several overlapping `O(S)` intermediates
increased copied bytes and peak RSS for large warning/error sets.

The cycle-free `query_rich_common` owner now assembles one fragment list: fixed
envelope literals, one cached count string, each existing diagnostic record with
comma separators, and the suffix. One final join creates the only full wrapper
output. Diagnostics remain embedded verbatim and in input order; empty, single and
multiple arrays retain the exact prior MCP envelope. The active rich-query path
and its older query-check predecessor both delegate to this owner, preventing
serialization drift.
