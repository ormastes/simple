<!-- codex-research -->
# MIR facts and escape-analysis audit lane

Scope: static source audit of the requested commit/worktree. No compiler, test,
or benchmark execution was performed. Line references below are evidence in the
audited tree, not runtime measurements.

## Executive result

The proposed shared `PerfFacts` direction is necessary. Today CFG successors,
predecessors, loop shape, induction/range facts, def-use, and alias/escape facts
are independently reconstructed by passes with incompatible semantics. Several
consumers then turn approximations into transformation proofs. The minimum safe
foundation is one immutable, function-revision-bound fact owner with explicit
preservation/invalidation; transforms must not use block order, textual keys,
or function-global proof pre-seeding as substitutes for dominance and memory
versions.

Escape analysis is reporting infrastructure, not allocation-placement evidence.
Its lattice API correctly says `Unknown` escapes, but `finalize()` converts every
unresolved allocation to `NoEscape`; the production analyzer does not record
returns; field store/load keys disagree at the integration boundary; and size is
not populated or gated. Stack promotion must remain disabled.

## Evidence: duplicated or conflicting MIR facts

### CFG and loop ownership

- `loop_detect.spl:101-120` classifies candidate backedges by block storage
  order. It subsequently rejects some false cycles using reachability, but it
  never computes dominance despite `LoopInfo` claiming the header dominates the
  loop (`loop_detect.spl:32-47`). A natural-loop transform therefore lacks its
  defining dominance proof.
- Every candidate calls `reachable_from` and `can_reach_target`; each rebuilds a
  whole successor or predecessor map (`loop_detect.spl:155-197`), and each
  worklist pop copies an array slice (`loop_detect.spl:165-173,188-196`). This is
  repeated graph construction plus avoidable allocation, not a cached linear
  function analysis.
- Loop consumers each own a mutable `LoopDetector`: loop optimization
  (`loop_opt.spl:73-88`), LICM (`loop_licm.spl:35-59`), collection optimization
  (`collection_opt_core.spl:28-41`), string building
  (`string_builder_opt.spl:27-40`). Passes cannot share results or invalidate
  them coherently after CFG mutation.
- Other passes implement their own CFG APIs: outlining owns a predecessor map
  (`outline.spl:45-75`) and another terminator-successor function
  (`outline.spl:536`); DCE has `get_successor_blocks` (`dce.spl:192`); SSA owns
  `ssa_terminator_successors` and repeated predecessor queries
  (`var_reassign_ssa.spl:616,666-721`).
- The loop detector's `trip_count` is actually an extracted comparison bound:
  it returns `N` for `i < N` or `N+1` for `i <= N` without proving the initial
  value, step, reachability of the definition, no-wrap, or signedness
  (`loop_detect.spl:276-285,332-385`). Calling it a trip count is unsound for
  transformation and inaccurate for cost analysis.

### Dominance, def-use, range, and alias facts

- GVN explicitly substitutes block order for dominator order and carries one
  value-number table across all blocks (`gvn.spl:133-151`). A value in a sibling
  or non-dominating block can become a leader. This is a correctness blocker,
  not merely missed optimization.
- Vectorization builds its own loop-local def-use chains
  (`auto_vectorize_analysis.spl:28-40,76-114`). Dependency classification uses
  flattened instruction order and treats multi-block forward dependencies as
  loop-carried (`auto_vectorize_analysis.spl:273-289`), rather than CFG/SSA
  reachability and dependence distance.
- Vector alias checking compares only equal base-local IDs; same-base `i` versus
  `i` is declared independent (`auto_vectorize_analysis.spl:295-333`). Distinct
  locals may alias, and same-base stores can conflict with shifted or otherwise
  derived indices. The separate production recipe itself admits it does not
  chase def-use or verify distinct bases and requires a future alias oracle
  (`_AutoVectorize/recipe.spl:307-333`).
- Vector loop bounds independently reconstruct loop structure and induction.
  Any constant on the right of an add is accepted as unit step, and the search
  scans every block in the function, including unrelated blocks
  (`auto_vectorize_analysis.spl:563-595`). Its body is only immediate non-exit
  header successors (`auto_vectorize_analysis.spl:613-632`), not a loop forest.
- BCE independently pattern-matches bounds. All collected loop proof keys are
  pre-seeded into every block (`bounds_check_elim.spl:77-109`), so proof scope is
  function-global rather than dominance/loop-region scoped. Guard recognition
  accepts a `Lt` between two locals as index and array without proving `len`, CFG
  loop membership, lower bound, or mutation relation
  (`bounds_check_elim.spl:233-287`). Its canonical dispatch wrapper is still an
  identity (`bounds_check_elim.spl:218-222`), which prevents current pipeline
  miscompilation but does not make the implementation activation-ready.
- CSE and GVN allocate textual expression identities (`cse.spl:56-83,105-136`;
  `gvn.spl:61-73`). This duplicates canonicalization, adds formatting/hash
  allocation in hot compile paths, and omits type/overflow/fast-math/memory
  version fields needed for semantic identity.
- Collection hoisting gathers local definitions itself and inserts alleged
  hoists at the start of the loop header (`collection_opt_patterns.spl:257-325`),
  so they still execute each iteration. LICM separately constructs and rewires a
  preheader (`loop_licm.spl:117-160`) but relies on local store-target equality,
  not alias/memory clobber facts, for load safety (`loop_licm.spl:164-188`).

## Escape-analysis correctness and readiness

### Confirmed blockers

1. **Unknown is unsafely promoted by finalization.** The lattice documents
   `Unknown` as bottom and says finalization demotes it (`escape.spl:27-40`). The
   query surface correctly treats `Unknown` as escaping and only `NoEscape` as
   stack eligible (`escape.spl:42-53`), but `finalize()` rewrites every untouched
   site to `NoEscape` and counts it eligible (`escape.spl:269-291`). Tests encode
   that behavior (`gc_safety_spec.spl:210-217`). Absence of a recorded escape is
   not proof of locality while instruction/terminator coverage is incomplete.
2. **Production returns are not recorded.** `EscapeAnalysis.record_return`
   exists (`escape.spl:237-242`) and unit tests call it directly
   (`gc_safety_spec.spl:219-225`), but `GcSafetyAnalyzer.process_terminator`
   explicitly does nothing for Return because return-value information is
   missing (`gc_analysis/mod.spl:263-271`). Thus the supplied audit's “return
   handling incomplete” is confirmed and made more precise: API present,
   integration absent.
3. **Field identity is inconsistent at the analyzer boundary.** Store and load
   methods themselves use the same `(type_id, field_idx)` tuple
   (`escape.spl:214-235`), contrary to the broad claim that their internal keys
   are differently formed. However, the caller passes `base_id_v` as the store
   type proxy and literal `0` on load (`gc_analysis/mod.spl:200-240`). A value
   stored then loaded through normal analyzer processing will usually not meet.
   Moreover the key is type-wide, ignores base allocation/region, and can merge
   unrelated objects of the same type.
4. **Flow-insensitive union never kills stale points-to facts.** Copies union
   source into destination (`escape.spl:207-212`), and new allocations add to an
   existing destination set (`escape.spl:174-186`). Reassignment cannot replace
   a definition's points-to set. This is conservative for escape classification
   but imprecise and can become costly; it also cannot produce per-program-point
   lifetime proofs.
5. **Field stores are always `FieldEscape`.** Every store marks the value as
   escaping regardless of whether the base is a proven local, non-escaping
   aggregate (`escape.spl:214-226`). This loses optimization but is not unsafe;
   a region graph should propagate escape from base/container instead.
6. **Unknown calls are fail-closed only accidentally/coarsely.** Every direct
   call argument is marked `ArgEscape` (`gc_analysis/mod.spl:245-258`), with no
   verified summaries, indirect-call distinction, parameter capture mode, or
   returned-alias propagation. This is conservative for arguments, but missing
   instruction arms combined with Unknown-to-NoEscape finalization is not.
7. **Size cannot gate promotion.** `AllocationSite` carries a presence flag and
   bytes (`escape.spl:74-102`), but `record_allocation` has no size parameter and
   the analyzer ignores MIR `Alloc` size (`gc_analysis/mod.spl:166-171`). No
   alignment, dynamic-size, frame-budget, or target-stack threshold exists.
8. **No proof provenance or placement consumer.** Reports expose only aggregate
   eligible counts/ratio (`gc_analysis/mod.spl:294-308`). There is no reason
   path, program-point-specific lifetime, exceptional-edge validation, GC-root
   differential evidence, or allocation rewrite in the inspected integration.
9. **Points-to set operations are array-linear.** Membership and union use
   `contains` and repeated push (`escape.spl:109-138`), giving growing-set
   quadratic behavior on merge-heavy functions.

### Contradictions/refinements to the supplied audit

- Refine “field points-to keys do not appear consistently formed between store
  and load”: the methods are consistent; their caller supplies inconsistent
  type proxies (`base local` versus `0`). The design fix is still required.
- Refine “Return handling is incomplete”: the state, API, and direct unit test
  exist, but terminator integration is a stub. This is stronger evidence than a
  missing enum/API.
- The supplied audit is correct that `Unknown` is converted to `NoEscape`; the
  current comments/tests explicitly bless this contradiction, so remediation
  must update semantics and tests, not merely implementation.
- Alias analysis is not simply absent. There are several narrow, disconnected
  approximations (vector base-local checks, LICM store-local checks,
  var-reassignment local alias roots, escape points-to). None is a reusable,
  dominance- and memory-version-aware oracle suitable for transforms.

## Proposed reusable ownership

Use the requested anchors as stable public vocabulary:

```simple
struct PerfFacts:
    revision: MirRevision
    cfg: CfgFacts
    dominators: DominatorFacts
    post_dominators: PostDominatorFacts
    loops: LoopForest
    def_use: DefUseFacts
    ranges: RangeFacts
    memory: MemoryFacts
    escape: EscapeFacts

struct LoopFact:
    header: BlockId
    preheader: Option<BlockId>
    latches: [BlockId]
    blocks: BlockSet
    exits: [CfgEdge]
    parent: Option<LoopId>
    depth: i64
    induction: Option<InductionFact>
    trip_count: TripCountFact

enum MemoryRegion:
    Stack(local: LocalId)
    Allocation(site: AllocationSiteId)
    Argument(index: i64)
    Global(symbol: SymbolId)
    Device(resource: ResourceId)
    Unknown
```

Ownership rules:

- `PerfFacts` belongs to a per-function analysis manager keyed by immutable MIR
  revision/fingerprint. Pass instances borrow facts; they do not own detectors.
- `CfgFacts` is the sole terminator-successor/predecessor authority and computes
  RPO once. `DominatorFacts` derives from it. `LoopForest` derives only from CFG
  plus dominance (backedge `latch -> header` requires header dominates latch).
- `LoopFact.trip_count` distinguishes `Exact`, `UpperBound`, and `Unknown`, with
  start, step, comparison, signedness, and no-wrap proof dependencies recorded.
- `DefUseFacts` records instruction/block program points and terminator uses;
  consumers query reaching definitions/dominance rather than flattened indices.
- `RangeFacts` is edge/path scoped. A guard refines facts only in dominated
  successor regions; mutation and memory clobber versions are explicit.
- `MemoryFacts` owns `MemoryRegion`, points-to/alias results, and MemorySSA-lite
  definitions/uses/phis. Ownership facts may prove disjointness; unsafe/raw or
  unresolved values collapse to `Unknown`. `Unknown` aliases/clobbers everything.
- `EscapeFacts` is a client of MemoryFacts plus verified callee summaries. A
  `NoEscape` result contains proof reasons and lifetime endpoints; unresolved
  paths remain escaping. Field identity is `(base region, field)` rather than a
  guessed type/local tuple.

### Preservation and invalidation contract

Each transform returns `PreservedFacts`, never informal dependency strings.

| Mutation | May preserve | Must invalidate/recompute |
|---|---|---|
| Replace pure scalar op, same operands/control | CFG, dominators, loops | def-use, ranges for result, value numbering |
| Insert/delete instruction | CFG, dominators, loops | instruction numbering, def-use; memory facts if memory/effecting |
| Rewrite terminator or block edges | none of CFG family | CFG, RPO, dominators, post-dominators, loops, ranges, MemorySSA |
| Add/remove/redirect preheader | local identities only | full CFG family and MemorySSA; reacquire facts before next transform |
| Change load/store/call/alloc | CFG family if edges unchanged | MemorySSA, aliases as applicable, effects, escape, costs |
| Change ownership/type/layout | CFG family | regions, aliases, escape, ranges tied to representation, layout/cost |

Facts must carry the MIR revision and reject queries after invalidation. A pass
that mutates CFG while iterating a previously acquired `LoopForest` must stop,
publish the revision, and reacquire facts.

## Activation gates and tests

Before any facts-dependent transform becomes `Active`:

1. CFG fixtures cover all terminators, unreachable blocks, critical edges,
   irreducible SCCs, nested loops, multiple latches/exits, and zero-trip loops.
2. Dominance/loop results are checked against explicit expected block sets;
   block permutation must not change them.
3. Range/BCE tests prove edge scoping, initial value, positive/non-unit steps,
   signed wrap, array-length mutation, alias mutation, and exceptional exits.
4. Def-use includes phi/terminator uses and redefinitions; vector dependence
   tests cover distinct locals aliasing, shifted indices, reductions, and calls.
5. Escape tests exercise production `GcSafetyAnalyzer`, not only direct helper
   methods: return, indirect/external call, aggregate/closure capture, local and
   escaping field base, globals, exceptional paths, and reassignment.
6. Unknown must remain non-stack-eligible. Every eligible site has size,
   alignment, frame-budget, proof reason, and end-of-lifetime evidence.
7. Heap-versus-promoted differential tests compare result, destructor/drop,
   GC roots, barriers, exceptions, zero-trip paths, and target backends.
8. Analysis complexity tests assert one CFG build/function revision and bounded
   points-to/cost-domain growth; telemetry counts cache hits, rebuild reasons,
   nodes, edges, and elapsed time.

## Priority recommendation

P0: keep GVN, BCE loop proofs, vector rewrite, LICM load hoisting, and stack
promotion disabled; fix the active collection header-hoist path or disable that
subtransform. P1: land `CfgFacts`/dominators/`LoopFact`/def-use and revisioned
invalidation. P1: make escape fail closed and repair production return/field
integration. P2: add `MemoryRegion` plus MemorySSA-lite and migrate consumers one
at a time. Only then rehabilitate transformations with semantic differential
gates and effective-pipeline telemetry.
