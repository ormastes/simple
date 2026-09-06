<!-- codex-research -->
# Optimizer registry, pipeline, and dispatch evidence

Scope: static source audit at `37bd406e219cc35cae049b4130f5167c21801864`. No compiler, tests, or benchmarks were executed. “Observed” statements are direct source facts; “Risk” statements require semantic or runtime validation.

## Executive finding

The supplied audit is correct that optimizer activation integrity is the first-order defect. `MirPassDescriptor` records name, aliases, provider, typed `PassKind`, scope, and cost, but has no operational status or transform expectation (`src/compiler/60.mir_opt/mir_opt/mod.spl:186-192`). Speed and Aggressive therefore advertise registered transformations without distinguishing working transforms from identity wrappers (`mod.spl:438-486`). Existing statistics count only named pass invocations, not candidates, transformations, instruction deltas, elapsed time, or missed reasons (`mod.spl:374-400`). No compiler optimizer implementation of the design anchors `PassStatus`, `PassExpectation`, `PassRunRecord`, or `PerfFacts` exists at this commit.

## Registry and canonical pipelines

**Observed.** `PassKind` provides typed identity for 25 pass kinds (`mod.spl:148-178`), and the registry maps public names/aliases to kind, scope, backend policy, and cost (`mod.spl:229-255`). Speed contains DCE, folding, propagation, GVN/CSE, TCO, outlining, LICM, BCE, vectorization, collection and string transforms (`mod.spl:438-459`); Aggressive additionally contains predicate promotion, unrolling, and strength reduction (`mod.spl:461-486`). Name lookup failing returns the input unchanged (`mod.spl:796-800`), so unknown requested passes also fail silently.

**Observed.** Typed function dispatch calls wrappers for the canonical pass kinds (`mod.spl:807-858`), and module dispatch repeats the same calls across module functions (`mod.spl:936-1014`). Thus typed dispatch removes string-switch ambiguity but does not establish that a pass executes its implementation.

**Risk.** Requested/effective pipeline truth cannot be reconstructed from `PassStatistics`: it records only pass names and total run count (`mod.spl:391-400`). A listed pass can appear successfully “run” while transforming nothing by construction.

## Verified identity transforms

The following are **observed unconditional identity wrappers** reached by canonical dispatch:

| Registered pass | Evidence | Recommended initial status |
|---|---|---|
| DCE | `dce_run_on_function` returns `func` (`mir_opt/dce.spl:440-442`) | `Disabled` |
| Constant folding | wrapper returns `func` (`mir_opt/const_fold.spl:558-560`) | `Skeleton` |
| Copy propagation | wrapper returns `func` (`mir_opt/copy_prop.spl:99-101`) | `Skeleton` |
| Local CSE | wrapper returns `func` (`mir_opt/cse.spl:371-373`) | `Skeleton` |
| GVN | wrapper returns `func` (`mir_opt/gvn.spl:391-392`) | `Disabled` |
| LICM and unrolling | both dispatch through the identity `loop_opt_run_on_function` (`mod.spl:829-834`; `mir_opt/loop_opt.spl:330-332`) | `Disabled` |
| BCE | wrapper returns `func` (`mir_opt/bounds_check_elim.spl:218-222`) | `Disabled` |
| Strength reduction | wrapper returns `func` (`mir_opt/loop_strength.spl:559-561`) | `Disabled` |
| String builder | wrapper returns `func` (`mir_opt/string_builder_opt.spl:261-262`) | `Disabled` |
| Generator state machine | wrapper returns `func` (`mir_opt/generator_sm.spl:608-610`) | `Skeleton` |
| TCO | wrapper returns `func` (`mir_opt/tco.spl:212-213`) | `Disabled` |
| Typed-byte canonicalization | class body and wrapper both return input; source calls it a structural skeleton (`mir_opt/typed_byte_canon.spl:35-47`) | `Skeleton` |
| Body outlining | function wrapper is identity and module loop body is empty (`mir_opt/outline.spl:706-723`) | `Skeleton` |

**Observed active exception.** Collection optimization calls its implementation (`mir_opt/collection_opt.spl:154-155`), which rewrites function blocks (`collection_opt.spl:31-46`). Module inlining also has dedicated module dispatch rather than the per-function no-op route (`mod.spl:957-965`). These require separate legality/profitability evidence; they are not identity transforms.

## Legality and cost blockers before activation

- **DCE — observed algorithm, derived cost/utility risk.** The dormant implementation scans the block for each result (`dce.spl:245-259`, `dce.spl:315-343`), then returns `true` when no same-block use exists to assume a possible inter-block use (`dce.spl:345-346`). This supports the audit’s quadratic local-scan and ineffective result-DCE concern. Replace with shared `PerfFacts.def_use`/backward liveness before activation.
- **GVN — observed correctness blocker.** Its own documentation says dominator order is approximated by storage/block order and the implementation iterates `func.blocks` (`gvn.spl:133-151`). Expression identities are interpolated text (`gvn.spl:343-367`). Activating the wrapper can reuse a value from a non-dominating path and adds avoidable allocation/hashing pressure. Require real dominators plus structural keys.
- **BCE — observed scope blocker.** Loop proofs are all inserted into one key set, and every block sweep is pre-seeded with every proof (`bounds_check_elim.spl:77-109`). Activating the wrapper could remove a matching check outside the proof’s dominated region. Require `PerfFacts` dominance/range-region attachment and mutation invalidation.
- **TCO — observed parallel-assignment blocker.** Recursive arguments are copied sequentially into parameter locals (`tco.spl:172-190`). A permutation such as `(a,b) -> (b,a)` can be clobbered if activated. Materialize every new argument in temporaries before parameter assignment.
- **Collection hoisting — observed placement blocker, semantic risk.** The active transform defines the loop set to include the header (`collection_opt.spl:48-56`) and inserts hoisted instructions at the beginning of that header (`collection_opt.spl:76-90`), not into a verified preheader. Therefore “hoisting” may still execute per iteration; if later changed to true preheader placement, zero-trip/trap/effect behavior must be proven. This active path needs a P0 audit.
- **Strength reduction — observed contract gap.** The provider advertises `non_negative_or_unsigned_operands` as required context (`loop_strength.spl:547-556`), while canonical dispatch supplies only a pass instance and function (`mod.spl:838-840`). Before activation, prove that each signed div/rem rewrite consumes an actual range/signedness fact from `PerfFacts`, rather than treating provider metadata as a proof.

## Contradictions and updates to the supplied audit

1. **Auto-vectorization is not AnalysisOnly at this commit.** Module dispatch invokes `run_auto_vectorize` (`mod.spl:1017-1020`). That routine explicitly rewrites accepted elementwise recipes and replaces the function (`mir_opt/_AutoVectorize/rewrite.spl:52-60`, `:77-117`); only reductions remain log-only (`:119-123`). Recommended status is `Active` for a narrowly described elementwise subset, with other recipe families `AnalysisOnly`/`Skeleton`.
2. **The vectorization legality concern is stronger, not obsolete.** `_is_index_increment` claims `i + 1` but accepts any small constant in 0–4 and does not prove operand identity (`rewrite.spl:149-160`); recipe matching uses that heuristic to select the induction destination (`recipe.spl:344-359`). Because a production rewrite now exists, this is an active correctness exposure rather than merely a future activation risk. It should fail closed until exact step-one, induction-use, dominance, trip-count, alias, and dependence proofs are supplied by `PerfFacts`.
3. **The identity count should include the shared loop wrapper as one dispatch choke point covering two registered pass names.** The supplied “at least eleven” remains conservative: the table above verifies thirteen registered pass entries whose canonical route is structurally non-operational (counting LICM and unroll separately).

## Required structural hardening

Extend `MirPassDescriptor` with the shared anchors:

- `PassStatus = Active | AnalysisOnly | RemarkOnly | Skeleton | Disabled(reason)`.
- `PassExpectation = MayTransform | MustTransformSentinel | NeverTransforms`.
- `PassRunRecord` carrying requested/effective identity, backend decision, functions/candidates/transforms, before/after instruction counts, elapsed time, and missed reasons.
- `PerfFacts` as the only reusable source for CFG, RPO, dominators, loop forest/preheaders, def-use, induction/range, region alias/effects, and MemorySSA-lite, with explicit preservation/invalidation.

CI must reject an `Active` canonical transform whose wrapper is structurally identity/empty, whose `MustTransformSentinel` remains unchanged, or whose provider-required proof inputs are unavailable. Effective pipelines must exclude `Skeleton`/`Disabled`, label analysis/remark-only entries, and report backend skips separately from optimizer inactivity.

## Evidence classification and next tests

Identity wrappers, registry membership, pipeline membership, dispatch paths, empty outlining loop, global BCE proof seeding, sequential TCO assignment, and active elementwise rewrite are observed facts. Miscompilation, compile-time regression, zero-trip changes, and runtime wins are derived risks/impacts requiring measurement. Each rehabilitation needs a positive sentinel, negative/adversarial MIR fixtures, before/after semantic differential execution, idempotence, malformed/irreducible CFG coverage, and explicit transform telemetry before its status may become `Active`.
