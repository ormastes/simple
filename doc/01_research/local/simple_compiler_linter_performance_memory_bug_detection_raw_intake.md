# Simple compiler and linter research: performance and memory bug detection

<!-- codex-research -->

> Intake status: incomplete source fragment. The received text ends mid-sentence at `Tier`; no missing claims were inferred.


Executive conclusion

Simple should implement performance diagnostics as a four-tier compiler service, not by continually adding source-pattern checks to the current standalone linter.

Tier

Runs in

Analysis budget

Appropriate work

Fast typed checks

simple check, editor/LSP, normal builds

One shared HIR traversal; local facts only

High-confidence collection, copy, allocation, layout, and API misuse lints

MIR optimization and remarks

Optimized builds

CFG, dominance, loop forest, use-def, local alias facts

Safe automatic transformations plus explanations for missed transformations

Deep performance analysis

simple perf --deep, CI

Cached interprocedural summaries, affine solvers, symbolic bounds

Accidental polynomial complexity, data-structure selection, peak-space bounds

Profile-guided diagnosis

Benchmarks and production sampling

Runtime counters/sampling

Rank findings by actual hotness, cardinality, allocation bytes, copying, and peak memory


The highest-priority work is not a new nested-loop rule. First, Simple needs to make the optimizer pipeline truthful and safe:

1. Several registered MIR transformation adapters currently return the input function unchanged.


2. The lint command is dominated by an extremely slow parser path.


3. Loop detection is not yet a sufficiently canonical foundation for aggressive loop transformations.


4. Escape and effect analyses are not yet sound enough to authorize memory transformations.



After those foundations are repaired, the existing CollectionPlan proposal is the correct architectural direction.


---

1. Current Simple repository audit

1.1 What already exists

Simple already has collection-efficiency diagnostics covering:

array concatenation in loops;

linear contains() inside loops;

front removal used as a queue;

selected loop-invariant calls;

chained filters;

string concatenation in loops;

array rebuilding to remove the last element;

unbounded global accumulation.


These are exposed as COLL001–COLL008, with COLL019 for mutation through indexed access. The linter has configurable moderate, strict, robust, and critical profiles.

The repository also already contains a substantial CollectionPlan design proposing:

COLL009 nested_dynamic_iteration;

COLL010 functional_linear_lookup;

COLL011 repeated_materialization;

COLL012 sequential_indexing;

COLL013 repeated_sort;

COLL014 unbounded_flat_map;

COLL015 accidental_cartesian_product;

COLL016 missing_index;

COLL017 complexity_regression;

COLL018 unknown_hot_callback_cost.


It proposes extracting collection operations after type/effect completion, constructing symbolic cost summaries, fusing pipelines, identifying index candidates, and lowering a plan before ordinary MIR optimizations. It also explicitly recommends bounded candidate sets, cached summaries, and restricting expensive analysis to hot or requested functions.

That proposal should become the center of the implementation rather than creating another unrelated analyzer.

1.2 Existing collection checks are too syntactic

The current collection_patterns.spl analysis operates on the AST before type inference. Several rules match method or operator names rather than resolved semantics:

.contains() can be identified without proving the receiver is a linear-time collection.

+ in a loop can be confused with non-string accumulation.

the current invariant-call rule recognizes a small list such as len, is_empty, first, and last;

it does not have a complete alias, mutation, purity, exception, or allocation model.


This explains both false positives and important blind spots such as functional pipelines and user-defined collection methods.

Recommendation: retain source-only checks as a fallback, but move performance-rule ownership to a typed HIR analyzer. Source-pattern checks should merely recognize unusually obvious cases when full compiler facts are unavailable.

1.3 The lint frontend is currently the performance bottleneck

The lint CLI first performs text checks, then invokes parse_module_silent_checked, and afterward runs AST-based rules. On this path, source spans are unavailable for some AST findings, so the linter searches source lines textually to reconstruct locations.

The repository’s measured lint-performance report corrected an earlier quadratic diagnosis: the observed growth is approximately linear, but with an enormous constant of roughly 0.19–0.20 seconds per line. Approximately 99% of the size-dependent lint time was attributed to parse_module_silent_checked; all roughly 44 lint checks together accounted for about 1%. A 600-line synthetic file took approximately 164 seconds in one measured family.

This leads to two decisions:

Adding several one-pass checks is not the current dominant cost.

The compiler, linter, and LSP must share one parsed and typed representation instead of reparsing separately.


The desired architecture is:

source
  └─ one parser result
       ├─ compiler
       ├─ linter
       ├─ formatter/source map
       └─ LSP

typed HIR facts
  ├─ correctness diagnostics
  ├─ fast performance diagnostics
  └─ MIR lowering

1.4 Several advertised MIR transformations have inert public adapters

The MIR pass manager and manifest system already define pass kinds, optimization levels, cost classes, backend policies, required facts, and produced facts. That is a good foundation.

However, representative public per-function adapters for loop optimization, CSE, DCE, constant folding, and copy propagation currently return the input function unchanged.

The same identity-adapter pattern appears in GVN, tail-call optimization, bounds-check elimination, and string-builder optimization.

This does not prove that downstream LLVM or another backend performs none of these optimizations. It does prove that these particular Simple MIR entry points do not transform their input. It also does not apply to every pass: collection_opt invokes its implementation, and the inliner has an active module-level driver despite its per-function facade being inert.

Before adding more optimizer passes, introduce a compiler-self-check:

Required pass contract

Rule

Explicit implementation status

Disabled, AnalysisOnly, Transform, or BackendDelegated

Positive witness

Every transform has a minimal input on which it must report changed=true

Negative witness

At least one non-candidate input must remain unchanged

IR verification

Verify CFG, SSA, types, dominance, and ownership after every changed pass in test/debug builds

Transformation statistics

Count candidates, transformed candidates, rejected candidates, and rejection reasons

Missed remark

A candidate rejected because of aliasing, effects, cost, or unavailable facts must explain why

Pipeline truth

A disabled transform must not be advertised as active at an optimization level


A pass legitimately performs no change on most functions. The defect is not “one invocation made no change”; it is “the advertised public adapter cannot change even its positive witness.”

1.5 Loop analysis needs a stronger canonical form

Simple’s loop detector has already been hardened after a previous false-loop interpretation involving break and block ordering caused an unsafe transformation. The current implementation constructs candidate headers from backward-looking block edges and then intersects forward and backward reachability to determine the cycle region.

This is useful, but aggressive fusion, LICM, unrolling, and scalar evolution need a stronger common foundation:

dominator tree;

natural loop forest and nesting;

canonical preheader;

one latch or normalized backedges;

dedicated exit blocks;

loop-closed SSA;

induction and recurrence facts;

zero-trip and finite-trip reasoning.


LLVM similarly places loop transformations on top of Loop Simplify form—preheader, single backedge, and dedicated exits—and uses LCSSA to make values crossing loop boundaries explicit.

1.6 Escape analysis must remain diagnostic-only for now

Simple’s escape lattice contains Unknown, NoEscape, argument, return, global, and field escape states. However:

finalization converts unresolved Unknown sites to NoEscape;

return terminators do not mark a returned allocation as escaping.


That is not conservative enough to authorize stack allocation or allocation elimination. An unresolved site must remain Unknown or MayEscape; failure to prove escape is not proof of non-escape.

The analysis should initially produce optimization remarks such as:

ESCAPE001: allocation remains on heap
reason: returned through unresolved aggregate path

Automatic stack placement should wait until the analysis handles at least:

direct and aggregate returns;

field/global stores;

closures and captured variables;

coroutine and async suspension;

thread/process handoff;

unknown and FFI calls;

interprocedural summaries;

aliasing through copies, moves, and option/sum variants.


1.7 Existing infrastructure can support memory lints

Simple already has architecture-aware type-layout computation exposing size, alignment, stride, field offsets, padding, and layout summaries.

That makes several Clippy-like diagnostics comparatively inexpensive:

large by-value argument;

large loop-variable copy;

large stack object or frame;

excessive struct padding;

large enum variant disparity, after variant layout is added;

alignment and cache-line warnings.


1.8 Existing profile infrastructure is reusable

The .sprof infrastructure already represents function, block, and edge counters, validates and merges profiles, and explicitly prohibits file opens, shell execution, and repository scanning in the hot path.

The compiler-side hotspot bridge maps function counts into JIT decisions.

A future .sprof-v2 can add memory and collection counters without creating an unrelated profiling system.


---

2. Where each diagnostic belongs

Finding type

Compiler transform

Default lint

Optimization remark

Deep/profile

Exact semantics-preserving local rewrite

Yes

Optional explanation

Yes

No

Likely bad API/data-structure choice

Usually no

Yes

Optional

Profile can rank

Layout or large-copy concern

No; API/layout may change

Yes

Yes for generated copies

Profile validates impact

Missed optimization caused by unknown alias/effect

No

Usually no

Yes

Deep analysis may resolve

Symbolic complexity increase

No

Only obvious cases

No

Yes, CI

Potential loop fusion with side effects

No

Possibly advisory

Yes

Profile/deep

Heap escape

Only after sound proof

No

Yes

Profile allocation bytes

Peak live-memory or retention

Rarely

Obvious patterns only

Yes

Primarily deep/profile

Cache locality, false sharing, AoS/SoA

Rarely automatic

Advisory

Yes

Primarily profile

Compiler pass itself is inactive/incorrect

Compiler CI failure

Not a user lint

Developer remark

Translation validation/fuzzing


A user warning should describe a likely source-level mistake. An optimization remark should explain a compiler decision. Mixing these produces noisy warnings for code that may already be optimized away.

LLVM distinguishes successful, missed, and analysis remarks and can serialize them for later processing. MLIR extends this with Failure, keeps the remark engine opt-in, and states that it has no overhead when disabled.

Simple should adopt the same separation:

simple check
    high-confidence source diagnostics

simple build -O2 --remarks=perf
    Passed / Missed / Analysis / Failure optimization records

simple perf --deep
    symbolic and interprocedural analysis

simple run --profile=perf,memory
    runtime evidence


---

3. Loop and algorithmic performance bugs to detect

The names below are provisional. Existing COLL009–COLL018 names should be retained where they already exist.

Candidate rule

Pattern

Required facts

Best placement

Safe action

Adjacent traversal fusion

Two or more adjacent loops traverse the same domain

Loop domain, order, read/write regions, effects, aliasing

MIR transform or missed remark

Fuse only after dependence and effect proof

COLL009 nested dynamic iteration

Loop over A contains a loop whose bound depends on runtime collection B

Loop bounds and cardinality symbols

Fast warning for obvious forms; deep bound analysis otherwise

Warn with inferred `O(

COLL010 functional linear lookup

map/filter/fold callback performs linear contains/find/index

Resolved collection operation cost and callback summary

Typed HIR

Suggest index/set construction

Multiple enumeration

Lazy/deferred sequence is counted, searched, then iterated again

Laziness and “enumerates argument” summaries

Typed HIR/interprocedural

Materialize once or combine operations

COLL011 repeated materialization

to_array, collect, clone, conversion, or copy repeatedly creates the same intermediate

Purity, aliasing, lifetime

HIR/MIR

Hoist/reuse; fuse if unobservable

COLL012 sequential indexing

Repeated x[i] on a sequential or non-random-access structure

Collection capability metadata
Typed HIR
Use iterator/cursor
COLL013 repeated sort
Sort occurs in a loop or on an unchanged value at multiple sites
Mutation version, aliasing, effect summary
HIR/MIR
Hoist or maintain an index
COLL014 unbounded flat-map
Output cardinality is a product or unknown expansion
Cardinality summaries
Deep check; profile ranking
Warn and report bound
COLL015 accidental Cartesian product
Two unrelated collection iterators with pair generation but no join predicate
Loop/pipeline plan and predicate relation
HIR/deep
Suggest keyed join/index
COLL016 missing index
Repeated scans by the same key across calls or loops
Query pattern summary, collection mutability
Interprocedural/deep
Recommend Dict, HashSet, sorted index, bitset
COLL017 complexity regression
Function bound degree or meaningful coefficient increases relative to baseline
Stable function identity and CostExpr
CI
Fail only on confident regression
COLL018 unknown hot callback cost
A hot map/filter/fold invokes a callback without a usable summary
Call summary plus profile hotness
Remark/profile
Request annotation or profile callback
Improved COLL004 invariant work
Pure, non-throwing, non-allocating expression is recomputed in loop
Dominance, memory version, effects
MIR LICM or remark
Hoist with zero-trip safety
Growth without capacity
Known/estimated N pushes into empty growable collection
Trip bound, initial capacity, mutation/escape
Typed HIR lint
Suggest reserve(N) or sized constructor
Duplicate associative lookup
contains(k) followed by get(k), or two identical lookups without mutation
Receiver/key identity, mutation version
Typed HIR
Use get, entry API, or cached lookup
Repeated normalization/hash/parse
lower, normalization, parsing, hash, serialization repeatedly applied to unchanged value
Purity and value version
HIR/MIR
Hoist/cache
Missed vectorization
Counted loop is vectorizable except for a known blocker
Loop dependence, alignment, target features
Optimization remark
Explain alias, stride, call, or reduction blocker
Poor memory stride
Inner loop walks a non-unit or cache-hostile dimension
Layout and affine index expressions
Remark/deep/profile
Loop interchange, tile, or layout suggestion
Tiny repeated kernel launch/offload
Small loops repeatedly cross CPU/GPU or process boundaries
Trip count and launch-cost metadata
Remark/profile
Batch or fuse launches


The .NET CA1851 rule provides a useful model for multiple enumeration: deferred sequences may execute expensive work or side effects each time they are enumerated, while materializing them trades repeated execution for memory.

Clang-tidy’s vector rule shows the value of a deliberately narrow high-confidence matcher: it recognizes loops with a derivable element count and recommends reserve rather than attempting a broad speculative rewrite.


---

4. Memory inefficiency bugs to detect

Candidate rule
Pattern or evidence
Fast/static feasibility
Placement and action

COPY001 hidden COW copy in loop
Mutation causes uniqueness check and deep clone on each iteration
High once COW operations are explicit in MIR
Compile warning; automatic evaluation/lifetime fix only with proof
COPY002 redundant clone/copy
Owned value is cloned, then original is never used
Medium local dataflow
Typed HIR/MIR lint with machine-applicable fix
COPY003 expensive iteration copy
Loop binds a large element by value but only reads it
High with layout and use analysis
Fast lint; use borrow/view
COPY004 large by-value parameter
Large or nontrivially copied parameter is read-only
High local use analysis
Fast lint; suggest reference/view, respecting API boundaries
COPY005 large return or assignment copy
Large value repeatedly copied across block/function boundaries
Medium
Remark or lint, depending on source visibility
LAYOUT001 large enum variant disparity
One variant determines a much larger enum stride
High after enum layout support
Lint only; boxing changes layout and ownership
LAYOUT002 large stack object/frame
Static frame estimate exceeds target threshold
High/medium
Lint or optimization analysis remark
LAYOUT003 excessive padding
Padding ratio or array stride waste exceeds threshold
High
Advisory lint; field reordering only where ABI permits
ALLOC001 allocation in hot loop
Allocating operation occurs in a loop
High statically, importance requires hotness
Remark; warn in @no_alloc or critical path
ALLOC002 repeated temporary collection
Pipeline materializes arrays between stages
High in CollectionPlan
Fuse/eliminate intermediate
ALLOC003 boxed element per collection entry
Pointer object allocated for every scalar/small value
High with representation metadata
Advisory lint
ALLOC004 allocating substring/slice
Copying substring used where a non-owning view is sufficient
High with lifetime proof
Lint/fix to slice/view
ESCAPE001 avoidable heap escape
Allocation escapes because of capture, interface conversion, unknown call, or return path
Medium/deep
Optimization remark first
RETENTION001 large capture across suspension
Large object or collection remains live across await, yield, callback, or task boundary
Medium liveness analysis
Lint/remark; narrow capture or extract needed fields
RETENTION002 retained capacity
Large backing buffer survives after logical size shrinks
Low statically
Profile-guided warning
RETENTION003 long-lived cache without bound
Global/member map or array only grows
High for simple cases
Fast lint, extending current unbounded-push rule
MEM001 duplicate conversion buffer
Repeated text/bytes/UTF/serialization conversion
Medium
HIR/MIR lint or caching remark
MEM002 peak temporary overlap
Two large temporaries are simultaneously live but could be sequenced or reused
Medium/deep liveness
MIR optimization or remark
CACHE001 AoS/SoA mismatch
Loop reads few fields from many large records
Low without workload facts
Profile/deep advisory
CACHE002 false-sharing candidate
Independently written fields or array elements share cache lines across worker partitions
Low statically
Concurrency-aware profile/annotation lint
CACHE003 pointer-chasing hot path
Linked/boxed structure dominates hot traversal
Medium structurally, impact requires profile
Profile-ranked advisory
STACK001 recursion/stack growth
Recursive depth bound times frame size exceeds budget
Deep symbolic analysis
Critical-mode error or report


Rust Clippy demonstrates useful confidence stratification here:

redundant_clone uses conservative use analysis;

large_types_passed_by_value uses target size;

large_stack_arrays and large_stack_frames are opt-in categories;

large_enum_variant explicitly warns that boxing can be counterproductive and should be measured.


Clang-tidy similarly warns about expensive range-variable copies and unnecessary value parameters only when read-only use can be established.

4.1 Hidden COW copies deserve a first-class Simple rule

The repository already contains a concrete Simple-specific example: mutating self.field.push(...) in a me method caused repeated deep copies. The report measured a 16,000-operation case improving from about 1.50 seconds to 0.09 seconds after fixing receiver/argument evaluation so uniqueness was preserved; a clone counter dropped from 2,000 to zero in a focused case.

The compiler should represent COW explicitly:

CowEnsureUnique(buffer)
CowClone(buffer, estimated_bytes)
CowMutate(buffer, operation)

A lightweight uniqueness dataflow can use:

Unique
Shared
Unknown
Moved
Escaped

Then report:

COPY001 hidden_cow_copy_in_loop
  loop bound: N
  copied value: self.items
  estimated copy bytes: N × size(self.items)
  reason uniqueness was lost:
      receiver and argument may refer to the same owner

In profile mode, record:

cow_clone_count;

cow_clone_bytes;

source/MIR site;

maximum cloned capacity;

loop/function hotness.


That combination catches both statically obvious and dynamically consequential cases.


---

5. Correct implementation of multiple-loop fusion

“Multiple loop” optimization encompasses several distinct problems:

Shape
Example
Main opportunity
Main danger

Sibling loops
Two loops read the same input and produce separate outputs
One traversal and shared loads
Changes global effect and exception ordering
Producer-consumer loops
First loop creates temporary, second consumes it
Eliminate or shrink temporary
Cross-iteration dependences
Repeated reductions
Separate sum, min, count traversals
One combined reduction
Floating-point/reduction semantics
Nested loops
Search B for every element of A
Index or join, not ordinary fusion
Accidental O(n²)
Functional pipeline
map().filter().map().collect()
Stream/collection fusion
Laziness, side effects, allocation timing
GPU/offload loops
Several small kernels over same buffers
Kernel fusion
Synchronization, register pressure, occupancy


MLIR’s affine fusion pass distinguishes producer-consumer and sibling fusion, contracts or removes temporary buffers, and uses a cost model because fusion can introduce redundant computation.

5.1 Required fusion proof

For adjacent loops L1 followed by L2, automatic fusion should require:

Equal or compatible iteration domains

lower1 == lower2
upper1 == upper2
step1  == step2
iteration_order compatible

Symbolic equality may be proved by scalar evolution or an affine solver.

Memory dependence safety

For every access pair:

L1.write ↔ L2.read
L1.write ↔ L2.write
L1.read  ↔ L2.write

The analysis must prove that interleaving iteration i of L2 immediately after iteration i of L1 does not violate a dependence that originally crossed iterations.

Affine array indexes can use direction or distance vectors. Non-affine pointer/collection accesses need region-based alias facts; unresolved aliasing rejects automatic fusion.

Effect safety

A fused execution changes:

L1(0), L1(1), ... L1(n-1),
L2(0), L2(1), ... L2(n-1)

into:

L1(0), L2(0),
L1(1), L2(1), ...

Therefore ordinary “both loops are independent” is insufficient. The bodies must be pure, or their effects must be proven to commute. Important blockers include:

I/O and logging;

mutation of shared or unknown state;

exceptions and panics;

allocation failure when observable;

atomics, volatile access, locks, and synchronization;

early break, continue, return, or yield;

nondeterministic calls;

callback effects;

externally visible destructor/finalizer timing.


Simple’s effect inference is a potential foundation, but unknown behavior must become an explicit top effect. Currently unresolved methods are handled conservatively in one path, while failed call synthesis or a catch-all expression can contribute no effects. That is not yet a sound purity proof.

Profitability

A legal fusion is not necessarily profitable. Use:

benefit =
    eliminated_traversal_cost
  + eliminated_or_contracted_temporary_bytes
  + shared_load_value
  + improved_locality
  - duplicated_computation
  - code_growth
  - register_pressure
  - vectorization_loss
  - parallelism_or_occupancy_loss

The static model can use approximate weights. Profile-guided mode should replace them with observed trip counts and hotness.

5.2 Fusion result levels

Confidence
Compiler behavior

Domain, dependence, effects, and profitability proved
Transform automatically
Legal but profitability uncertain
Emit Analysis remark; use profile if available
Likely profitable but alias/effect fact missing
Emit Missed remark naming the exact blocker
Source structure suggests fusion but semantics cannot be proved
Optional lint/advisory, never automatic
Effects or dependence prove it unsafe
No user warning unless source design itself is suspicious



---

6. Proposed performance-analysis IR

The existing CollectionPlan should be augmented with shared cost and memory summaries.

6.1 Symbolic resource expressions

CostExpr =
    Zero
    Constant(i64)
    SizeOf(ValueId)
    Add([CostExpr])
    Multiply([CostExpr])
    Maximum([CostExpr])
    Log2(CostExpr)
    Unknown(Reason)

Do not initially attempt arbitrary closed-form mathematics. A bounded algebra of constants, input sizes, sums, products, maxima, and selected logarithms covers most actionable accidental-complexity findings.

6.2 Function summary

PerfSummary:
    time_steps: CostExpr
    collection_traversals: Dict<CollectionOrigin, CostExpr>

    allocation_count: CostExpr
    allocation_bytes: CostExpr
    copied_bytes: CostExpr
    stack_bytes: CostExpr
    peak_live_bytes: CostExpr?

    reads: RegionSet
    writes: RegionSet
    effects: EffectSet

    enumerated_arguments: BitSet
    returned_aliases: AliasSummary
    escaping_arguments: BitSet

    confidence: Proven | Conservative | Heuristic | Profiled
    unknown_reasons: [Reason]

6.3 Collection operation metadata

Standard-library operations should expose metadata generated with the library build:

CollectionOperationSummary:
    receiver_kind
    lazy_or_eager
    preserves_order
    may_allocate
    may_copy
    enumerates_receiver_count
    enumerates_argument_mask
    result_cardinality
    lookup_cost
    append_cost
    random_access
    stable_reference_behavior

User-defined functions get inferred summaries. Unknown functions remain unknown; they must not silently become O(1), pure, or non-allocating.

6.4 Analysis pipeline

typed HIR
  │
  ├─ resolve collection operations and receiver capabilities
  ├─ compute type layout and copy costs
  ├─ compute conservative effect facts
  └─ extract CollectionPlan
          │
          ├─ pipeline/traversal fusion
          ├─ local complexity diagnostics
          ├─ index/data-structure candidates
          └─ lower to MIR
                  │
                  ├─ CFG + dominators + loop forest
                  ├─ use-def and liveness
                  ├─ region alias / memory versions
                  ├─ induction and trip bounds
                  ├─ COW uniqueness / escape facts
                  └─ transformations + remarks
                          │
                          └─ cached interprocedural summaries
                                  │
                                  ├─ deep symbolic analysis
                                  └─ profile correlation


---

7. Keeping compile and lint cost low

7.1 Analysis tiers

Analysis
Expected shape
Default

One typed HIR visitor collecting calls, loops, allocations, and collection operations
Linear in HIR size
Always
Type layout lookup
Cached per type/target
Always
Local variable version/use analysis
Linear or near-linear
Always for changed functions
CFG, dominators, loop forest
Near-linear in MIR graph
Optimized builds and perf remarks
Local region aliasing
Bounded per function
Optimized builds
Interprocedural summaries
SCC fixed point over compact summaries
--perf or cached background analysis
Presburger/affine dependence
Candidate loops only
Deep mode or affine kernels
Symbolic resource solver
Candidate functions with size symbols
Deep/CI
Polyhedral transformation search
Selected kernels only
Explicit opt-in
Full peak-heap/GC analysis
Selected critical components
Explicit verification mode
Runtime allocation/cardinality instrumentation
Sampled or thresholded
Profile builds


7.2 One traversal, not one traversal per rule

Do not let every lint recursively walk HIR. A single fact collector should emit events such as:

enter_loop(loop_id)
call(call_id, resolved_callee)
collection_op(op)
allocation(site, type)
copy(site, type)
read(region)
write(region)
suspend(site)
leave_loop(loop_id)

Rules then consume indexed facts.

7.3 Incremental summaries

Cache each summary under:

hash(
    canonical typed HIR or MIR,
    imported summary hashes,
    target layout,
    optimization configuration,
    standard-library cost-model version
)

Only callers whose imported summary changed need reanalysis.

ThinLTO demonstrates the scalability value of compact summary-only whole-program analysis followed by parallel per-module optimization rather than loading all IR into one serial optimizer.

7.4 Bounded analysis and explicit incompleteness

Every expensive analysis needs:

maximum function/MIR size;

maximum loop-candidate count;

maximum SCC size;

solver timeout;

cancellation for editor use;

cached result reuse;

an explicit AnalysisIncomplete(reason) result.


Do not translate timeout or missing facts into “safe,” “pure,” “non-escaping,” or O(1).


---

8. Static and dynamic complexity regression detection

8.1 Static differential analysis

Store a compact .sperf record:

function stable ID
source/MIR hash
time bound
allocation-count bound
allocation-byte bound
copy-byte bound
stack bound
confidence
assumptions

CI compares old and new summaries:

Change
Default response

O(n) → O(n²)
Error for changed function
O(n log n) → O(n²)
Error
Same degree, much larger known coefficient
Warning or budget failure
Known bound → unknown
Warning; error in performance-critical code
Unknown → known
Improvement record
Allocation count O(1) → O(n)
Warning/error by policy
Peak space O(n) → O(n²)
Error in deep/critical mode


Infer Cost already follows this general model: it computes symbolic upper bounds and can use report differences to detect complexity changes.

SPEED shows that interprocedural symbolic bounds can be derived using counter instrumentation and invariant generation, including bounds dependent on scalar inputs and quantitative properties of heap structures.

8.2 Empirical complexity curves

Static analysis will often return unknown for highly dynamic code. Add:

simple perf curve benchmark_name \
    --size 100,200,400,800 \
    --metric time,alloc_bytes,cow_clone_bytes

Fit the scaling exponent after subtracting fixed startup cost:

metric ≈ c × n^k

Use confidence intervals and several repetitions; never infer O(n²) from a single timeout.

The repository’s lint-performance investigation is a good example: fitting multiple uncensored measurements showed an exponent near one, correcting the earlier quadratic interpretation while still exposing an unacceptable constant.

Static and empirical findings should reinforce each other:

static: traversals = n × m
profile: m ≈ n
result: observed exponent ≈ 2


---

9. .sprof-v2 extensions

The existing function/block/edge counter format can be extended with optional records:

Record
Data

loop
entries, backedges, total iterations, maximum trip count, histogram/sketch
collection
operation, receiver type, cardinality sketch, result cardinality
allocation
count, requested bytes, retained capacity, lifetime class
copy
count, bytes, source/destination type
cow_clone
count, cloned bytes, previous sharing state
escape
allocation site and observed destination class
suspend_retention
bytes live across await/yield
cache
optional hardware samples such as misses and false-sharing indicators
remark_outcome
candidate accepted/rejected and whether profile later supports decision


Profile-guided diagnostics should be ranked by estimated waste:

estimated_waste =
    execution_count
  × avoidable_cost_per_execution

For example, a source-level nested scan in a cold administrative command should rank below a small avoidable allocation executed billions of times.

Sampling-based profile-guided optimization has been used to lower collection overhead relative to full instrumentation while retaining useful optimization benefit, illustrating why Simple should support both exact test instrumentation and low-overhead production sampling.


---

10. Prior-art comparison

System or research
Detects or enables
Main lesson for Simple

Infer Cost
Symbolic execution/allocation bounds and differential complexity changes
Implement a compact CostExpr, preserve unknown reasons, and make regressions a CI feature rather than a noisy default lint.
SPEED
Interprocedural symbolic execution-count bounds
Counter and invariant summaries can detect serious modular complexity regressions without fully interpreting every implementation.
LLVM loop infrastructure
Canonical loop forms, LCSSA, scalar evolution
Build trustworthy loop facts before enabling LICM, fusion, unrolling, or strength reduction.
MLIR affine fusion
Producer-consumer and sibling fusion, temporary contraction, cost modeling
Preserve collection/affine structure until decisions are made; legality and profitability are separate questions.
LLVM/MLIR remarks
Passed, missed, analysis, and failure optimization records
Do not report every missed optimization as a source warning; provide structured opt-in records.
Rust Clippy
Redundant clones, large copies, stack frames, layout waste
Use target layout, conservative local use analysis, confidence groups, and fix applicability.
clang-tidy
Missing capacity reservation, costly range copies, costly value parameters
Narrow, high-confidence patterns provide value without requiring whole-program proof.
.NET CA1851
Multiple enumeration of deferred collections
Collection metadata must distinguish lazy enumeration from already-materialized random-access collections.
Go compiler/gopls
Escape, bounds, nil-check, and inlining optimization details
Optimization details should be opt-in and delayed/cached in the editor, while ordinary diagnostics remain immediate.
Futhark
Array fusion, memory IR, layout transformations, GPU-oriented memory optimization
High-level array/collection structure and explicit memory descriptors enable transformations that are difficult after low-level lowering.
RaML/AARA
Automatic time, heap, stack, and amortized resource bounds
Appropriate for selected critical functions or CI, not an always-on editor analysis.
Cozy
Synthesizes efficient collection implementations from query specifications
Use query-pattern summaries as an offline data-structure adviser; do not silently replace containers whose ordering or ownership semantics differ.
Alive2
Bounded translation validation of LLVM transformations
Add refinement-style validation for local Simple MIR transformations; acknowledge bounded and interprocedural limitations.
Optimuzz
Optimization-directed fuzzing combined with translation validation
Generate programs specifically shaped to activate each optimization, rather than relying only on ordinary random compiler fuzzing. Its LLVM/TurboFan evaluation reported 55 new miscompilation bugs.



---

11. Optimizer correctness and validation plan

Simple’s previous loop-detection bug and current identity adapters show that performance work needs stronger evidence than “the pass file exists” or “a test returned green.”

11.1 Required tests per transformation

Test class
Required evidence

Activation witness
Exact candidate count and changed=true
Non-candidate
No change and an appropriate rejection reason
Zero-trip loop
Same behavior when loop executes zero times
One-trip and multiple-trip
Boundary correctness
Alias trap
Transformation rejected when two paths may alias
Effect trap
Transformation rejected for I/O, mutation, throw, atomic, volatile, or unknown callback
Control-flow trap
break, continue, return, unwind, and unreachable blocks
Overflow/signedness
Integer transform matches language overflow semantics
Ownership/COW
Copies, moves, uniqueness, and destruction timing remain correct
Differential execution
Optimized and unoptimized executions agree on generated inputs
IR verification
SSA, dominance, CFG, types, and ownership invariants hold
Performance witness
Benchmark proves the transformation affects the intended metric
Pass-disabled control
Removing/disabling the pass makes the positive witness fail to transform


11.2 Compiler developer modes

--verify-each
--print-pass-stats
--remarks=passed,missed,analysis,failure
--opt-bisect-limit=N
--dump-before=pass
--dump-after=pass
--validate-transform=pass

The previous dead effect-analysis implementation in Simple illustrates why positive controls matter: the implementation was unreachable, the main pipeline did not call it on ordinary builds, and a vacuous test using an empty module still passed. It was later deleted after execution-based reachability checks.


---

12. Recommended implementation sequence

Phase 0 — make existing optimization claims trustworthy

Work
Acceptance condition

Add pass implementation status
No pass is silently represented as active while its public adapter is a permanent identity
Add positive activation witnesses
Every enabled transformation changes at least one dedicated MIR specimen
Add pass statistics and remarks
Candidate, changed, and rejected counts are observable
Add --verify-each
Every changed pass is followed by structural verification
Fix lint parser execution cost
Lint reuses compiler parse/cache; no separate full parse for already-compiled files
Preserve real source spans
AST/HIR diagnostics no longer recover primary locations by textual guessing


Phase 1 — typed high-value lints

Implement first because they are inexpensive and highly actionable:

1. typed replacements for COLL001–COLL008;


2. COPY001 hidden_cow_copy_in_loop;


3. multiple deferred enumeration;


4. growth without capacity;


5. expensive loop-variable copy;


6. large by-value parameter;


7. redundant clone/copy;


8. duplicate map lookup;


9. repeated sort/materialization;


10. allocating substring where a view is valid;


11. large stack object/frame;


12. padding and large-layout diagnostics.



These should share one HIR fact collector and the existing type-layout subsystem.

Phase 2 — sound local MIR facts

Component
Required before

Dominator tree and canonical loop forest
LICM, fusion, unrolling
Def-use and liveness
redundant copy, stack frame, temporary overlap
Memory-version/region alias facts
CSE, GVN, LICM, fusion
Explicit unknown effect
any movement or fusion of calls
COW uniqueness analysis
clone elimination and COPY001 precision
Conservative escape analysis
stack allocation or allocation elimination
Scalar evolution/trip bounds
reserve suggestions, unrolling, complexity bounds


Phase 3 — CollectionPlan execution

Activate the existing design:

type/effect completion
  → collection plan extraction
  → local complexity summary
  → stream/pipeline fusion
  → index candidates
  → cost-based planning
  → MIR lowering

Initially transform only:

pure pipelines;

exact same-domain loops;

non-escaping intermediates;

cases with proven order and dependence safety.


Everything else emits structured remarks.

Phase 4 — interprocedural and differential complexity

Implement:

compact function summaries;

imported-summary caching;

SCC fixed-point propagation;

COLL009–COLL018;

.sperf baseline files;

complexity and allocation regression CI;

@performance_critical and @no_alloc policy reachability;

explicit unknown/timeout reporting.


Phase 5 — deep and profile-guided analysis

Add selectively:

affine dependence and loop transformation;

AARA-style resource bounds for critical pure/ownership-disciplined code;

profile-ranked data-structure suggestions;

loop/cardinality/allocation/COW counters in .sprof-v2;

empirical complexity curves;

profile-guided fusion and layout recommendations;

hardware-sampling correlation for locality and false sharing.



---

13. Recommended first-release rule set
The best first release is a small, precise set rather than dozens of heuristic warnings.
Priority
Rule
Why first
1
Compiler pass activation conformance
Prevents false claims that optimization exists
2
COPY001 hidden COW copy in loop
A proven severe Simple-specific defect class
3
Multiple deferred enumeration
Common, precise, and may also duplicate side effects
4
Nested linear lookup
Directly catches accidental O(n²) behavior
5
Repeated sort/materialization
High cost and usually easy to explain
6
Growth without reserve
Cheap analysis and low-risk fix
7
Expensive loop-variable copy
Reuses layout plus local read-only analysis
8
Large by-value parameter/stack object
Reuses existing target layout
9
Duplicate associative lookup
High confidence and easy rewrite
10
Improved loop-invariant work
Valuable after effects, aliasing, and zero-trip correctness
11
Allocation/COW optimization remarks
Makes compiler decisions visible without noisy warnings
12
Complexity regression CI
Prevents recurrence after individual patterns are fixed
Final architectural recommendation
The correct end state is:
                     ┌───────────────────────────────┐
                     │ Shared parsed + typed program │
                     └──────────────┬────────────────┘
                                    │
                  ┌─────────────────┴─────────────────┐
                  │ Fast typed PerfFacts             │
                  │ types, layout, effects, copies,  │
                  │ collections, allocations         │
                  └─────────────────┬─────────────────┘
                                    │
               ┌────────────────────┴────────────────────┐
               │                                         │
     high-confidence lints                    CollectionPlan + MIR facts
                                                       │
                                      ┌────────────────┴───────────────┐
                                      │ transforms + structured remarks │
                                      └────────────────┬───────────────┘
                                                       │
                                   cached interprocedural CostSummary
                                                       │
                           ┌───────────────────────────┴─────────────────┐
                           │                                             │
                   deep/CI bounds                               .sprof evidence
This maximizes coverage without making normal compilation heavy:
obvious problems are caught immediately;
safe opportunities are optimized;
uncertain opportunities are explained rather than guessed;
expensive analyses run only where requested or justified by hotness;
runtime evidence resolves questions that static analysis cannot answer reliably;
every optimizer pass must prove both that it activates and that it preserves semantics.
