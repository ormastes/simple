<!-- codex-system-test -->
# Collection planner system test plan

Status: design draft. The user selected the full functional scope in
`doc/02_requirements/feature/collection_planner.md` and balanced targets in
`doc/02_requirements/nfr/collection_planner.md`. No collection-planner system
spec, generated manual, or passing full CLI runner exists yet. Existing unit
and DataFrame specs below are narrower evidence and do not close a system
requirement.

Executable home: `test/03_system/app/compiler/feature/collection_planner_spec.spl`.
Generated manual: `doc/06_spec/03_system/app/compiler/feature/collection_planner_spec.md`.

## Traceability and required scenarios

Each row needs at least three independent executable scenarios: the normal
behavior, a semantic edge, and a rejected or unsupported case. The system
spec must invoke production entrypoints and inspect observable results or
durable plan receipts. A source-shape assertion or canned helper result is
not acceptance evidence.

| REQ | Existing narrower evidence | Required system scenarios | Status |
|---|---|---|---|
| 001 | `test/03_system/feature/scilib/df_merge_spec.spl`, `df_groupby_spec.spl`, `df_value_counts_spec.spl`, `df_scalar_broadcast_spec.spl`; `doc/06_spec/03_system/feature/scilib/` mirrors exist but need freshness checks | Typed column round trip; signed zero/NaN/duplicate/missing edge; dtype mismatch rejected | Partial; generic typed column missing |
| 002 | None across all five engines | Map/filter/flat-map/any/all parity; captured closure and Dict collision parity; missing runtime symbol fails build | Missing |
| 003 | `test/01_unit/compiler/semantics/hir_perf_facts_spec.spl` exercises an in-memory registry | Production registry binding; duplicate/stale row rejected; backend symbol mismatch rejected | Partial; no production registry load |
| 004 | Numeric DataFrame specs above | Generic unique/group_by first-seen order; collision and fallback behavior; operation-count scaling | Partial; generic indexed algorithms missing |
| 005 | Text-only hash collection specs, if admitted, are narrower than generic-key parity | Integer/text/enum/tuple/symbol keys; collision/resize/removal; unsupported hash/equality rejected | Missing |
| 006 | `test/01_unit/compiler/semantics/hir_perf_facts_spec.spl` and existing `COLL` lint specs | Equivalent chain/loop warnings; bounded intentional work suppressed; strict-mode assumptions explained | Partial; no production typed equivalence |
| 007 | `test/01_unit/compiler/semantics/collection_plan_spec.spl` and `collection_plan_extractor_spec.spl` | Chain and loop extract equivalent DAGs; unknown facts block rewrite; malformed or cyclic plan rejected | Partial; no production invocation |
| 008 | None for emitted fused MIR | Pure map/filter parity and allocation count; callback/throw/mutation/short-circuit edge; unproven case uses original path | Missing |
| 009 | `test/01_unit/compiler/mir_opt/collection_plan_selection_spec.spl` is only an advisory chooser | Semi/anti/first/all/index candidate parity; duplicate/order/output-work edge; illegal candidate rejected with reason | Missing production lowering |
| 010 | In-memory `.sprof` work is provisional until wired to the compiler | Valid profile changes guarded choice; stale/mismatched profile ignored; missing profile preserves original behavior | Missing production adaptation |
| 011 | No system explain or differential evidence | Selected and rejected plan explanation; differential multi-engine oracle; selected NFR scaling/RSS gate | Missing |

Recently appearing untracked explain/profile files in the shared worktree are
treated as concurrent work until their owner completes and verifies them.
They are not counted as accepted evidence here.

## Environment and execution order

1. Use an admitted pure-Simple compiler and compiled SPipe runner. Interpreter
   mode alone loads `it` blocks without executing them. Keep the Rust seed and
   bootstrap-only diagnostic binaries out of release evidence.
2. Prove REQ-002 on the same deterministic fixtures in interpreter, JIT,
   LLVM AOT, self-hosted native, and bootstrap routes before enabling source
   lambda repair or synthesized Dict indexes. Capture command, exit status,
   output, runtime-symbol audit and artifact hashes for each route.
3. Cover typed columns, generic hash keys, standard-library order and
   complexity (REQ-001/004/005). Use fixed adversarial collision fixtures and
   NaN, signed-zero, duplicate and missing-value cases.
4. Cover registry, diagnostics and logical extraction (REQ-003/006/007).
   Capture the typed source span, resolved symbol, registry version, fact
   receipt, blockers and exact original HIR fallback.
5. Cover fusion and equality-key physical lowering (REQ-008/009). Compare
   results, callback count/order, exceptions, allocations and selected MIR
   against the unfused original on every supported backend.
6. Cover `.sprof`, explain output and selected NFR thresholds (REQ-010/011).
   Profiles must be tied to function, target, backend, registry and epoch;
   invalid profiles must not legalize a rewrite.

Fixtures must use deterministic seeds and bounded input sizes for ordinary
system runs. The scaling lane uses 1k, 2k, 4k and 8k indexed workloads with
bounded output multiplicity; its endpoint operation-count exponent must be at
most 1.15. Record all four counts and separate all-equal output costs. Compare
at least five warm runs per fixture against the same-revision unoptimized
baseline: at most 10% median wall-time, 20% median peak-RSS and 5% warm
compiler startup/request latency regression. Measure cold startup without a
numeric gate. Do not use elapsed time
alone as an algorithmic oracle. Fold backend/edge/stress matrices in the
generated manual while keeping primary scenario steps visible. Capture
text/exec/log/artifact evidence; no screenshot is needed for the explain TUI.

## Pass criteria and manual generation

All 33 minimum scenarios must contain real assertions and pass in compiled
mode; no `pass_todo`, tautological assertion, silent helper or fake receipt is
accepted. Every algorithm-changing rewrite needs differential and scaling
evidence. Run `simple spipe-docgen <spec> --output doc/06_spec --no-index` after
writing the spec; require `0 stubs`, review the mirrored Markdown, and confirm
no executable `.spl` remains under `doc/06_spec`. Run each acceptance criterion
once per session and stop after the repository's three verify/fix cycles.

## 2026-10-03 concrete acceptance inventory (append-only update)

The selected scope is still REQ-001–011 and NFR-001–007. The canonical
executable now contains CP-GUARD-01–06, a selector/explanation integration
slice only. Its presence supersedes the opening statement that no system
spec exists; it does not close any full requirement. The 33 cases below are
**planned, not executed or passing**. They require real production entrypoints,
not source-text checks, invented receipts, or test-side alternative engines.

Every A/B/C row is a separate acceptance case; comma-separated subcases are
fixture variations. Capture source/runtime/compiler digests, backend and target,
registry/profile identity, exit status, stdout/stderr, exact output values and
callback trace. Negative fixtures must reject for the named cause, not merely
fail compilation for an unrelated missing import.

| ID / requirement | Concrete fixture and independent oracle | Execution evidence required |
|---|---|---|
| CP-001-A / REQ-001 | Typed i64 `[10,20,30]`, missing `[false,true,false]`; dynamic roundtrip preserves values and mask; map `+1` yields present 11 and 31 with exactly two callback calls | Real typed/dynamic adapters and callback trace |
| CP-001-B / REQ-001 | Numeric `[+0,-0,NaN,2,2]`; zero keys match, NaN never matches, duplicate 2 rows retain source order; all-missing any=false/all=true with zero callbacks | Actual numeric join/column outputs including mask and source row IDs |
| CP-001-C / REQ-001 | Convert f64 dynamic column as i64; mask lengths 2 and 4 for three rows; negative and end index | Explicit DType/shape/index errors, no callback or partial result |
| CP-002-A / REQ-002 | `[1,2,3]`: map `*2` => `[2,4,6]`, filter odd => `[1,3]`, flat-map `[x,-x]` => `[1,-1,2,-2,3,-3]` | Same fixture and oracle on interpreter/JIT/LLVM AOT/self-hosted native/bootstrap routes, using admitted self-hosted toolchain |
| CP-002-B / REQ-002 | Closure captures 7, maps => `[8,9,10]`; any `x==2` visits `[1,2]`; all `x<2` visits `[1,2]`; Dict collision keys preserve values | Exact captures, callback traces, short-circuit and Dict outputs on all engines |
| CP-002-C / REQ-002 | Isolated backend capability fixture deliberately omits one referenced closure runtime symbol | Build rejects exact missing symbol before running output; no seed fallback |
| CP-003-A / REQ-003 | Registry binds two same-spelling methods with different resolved symbol/receiver types | Lint and planner consume only matching versioned row, not method-name guesses |
| CP-003-B / REQ-003 | Warm compile twice; change registry version and then callee summary independently | One initial load, cache hit unchanged, affected-function miss on each identity change |
| CP-003-C / REQ-003 | Duplicate resolved row, stale schema, advertised unavailable backend symbol | Deterministic configuration errors before rewrite; no partial admitted registry |
| CP-004-A / REQ-004 | Unique `[3,1,3,2,1]` => `[3,1,2]`; group by parity => first key odd rows `[3,1,3,1]`, then even `[2]` | Actual stdlib indexed implementation plus first-seen key/row order |
| CP-004-B / REQ-004 | Constant-hash distinct keys, repeats and empty input | Exact unique/group results; collisions never merge unequal keys; empty returns empty |
| CP-004-C / REQ-004 | 1k/2k/4k/8k supported integer keys; unsupported hash-key fixture separately | Actual operation counters meet NFR-002; unsupported keys retain documented fallback, never claim indexed scaling |
| CP-005-A / REQ-005 | Map/set integer, text, enum, tuple, interned-symbol keys; insert/get/contains/remove | Per-engine exact values, set cardinality, equal-key replacement semantics |
| CP-005-B / REQ-005 | Constant-hash keys crossing resize boundary, remove middle chain key, reinsert | Surviving keys remain reachable, removed key absent, replacement doesn't duplicate |
| CP-005-C / REQ-005 | Key lacks hash/equality contract; unequal keys deliberately share hash | Unsupported contract rejects index; valid collisions preserve distinct keys |
| CP-006-A / REQ-006 | Functional contains-in-filter and equivalent explicit nested loops on same typed keys | Same complexity class and COLL candidate; source-located spans differ appropriately |
| CP-006-B / REQ-006 | Intentional loop with proved size bound 4; identical shape without proof | Bounded diagnostic suppression only with proof; explain carries bound source |
| CP-006-C / REQ-006 | Unknown effect/key equality in strict mode; method with misleading collection name | Explicit assumption/blocker, no typed cost invented from method spelling |
| CP-007-A / REQ-007 | Typed map/filter chain and equivalent recognized loop | Production extraction yields equivalent topology/types/order/cardinality, actual resolved symbols and spans |
| CP-007-B / REQ-007 | Drop equality/alias/effect witness one at a time | Explicit unknown blocker and unchanged original HIR fallback; no rewrite |
| CP-007-C / REQ-007 | DAG with forward edge, self-cycle, wrong arity, nonfinal output and disconnected node | Structural validator rejects each case before selection |
| CP-008-A / REQ-008 | Pure map `+1`, filter even on `[1,2,3]` => `[2,4]` | Emitted MIR has one loop/output builder and no intermediate arrays/closures; executed block counters confirm lowered loop ran |
| CP-008-B / REQ-008 | Eager map/filter callbacks append `m1,m2,m3,f2,f3,f4`; callback returns error on second input; alias mutation, suspension and any/all fixtures | Original vs candidate output, trace, first error and suspension order identical; unsafe fusion rejected |
| CP-008-C / REQ-008 | Pure-looking callback with unknown external effect or escaping collection | Original selected and executed; no optimized block visits, explicit proof blocker |
| CP-009-A / REQ-009 | Left row IDs/keys `[(L0,2),(L1,1),(L2,2)]`, right `[(R0,2),(R1,2),(R2,3)]` | Semi `[L0,L2]`, anti `[L1]`; nested/hash/merge/direct candidates compared only when their proofs apply; selected algorithm actually executes |
| CP-009-B / REQ-009 | Same rows; first matches `(L0,R0),(L2,R0)`; all matches `(L0,R0),(L0,R1),(L2,R0),(L2,R1)`; all-equal n by m | Exact duplicate/order oracle, output work n*m charged independently of lookup work; overflow-safe cardinality arithmetic |
| CP-009-C / REQ-009 | Valid hash candidate over memory cap; unknown key equality; critical policy hash request; stale mutation epoch | Explicit rejection and actual original fallback; no allocation above cap; no profile override of legality |
| CP-010-A / REQ-010 | Same site cold/small versus admitted hot/large profile | Guarded cost choice changes and emitted/visited physical plan matches choice; identical results |
| CP-010-B / REQ-010 | Missing profile then mutate source/function, backend, target, key, registry and epoch individually | Each mismatch ignored with reason, no stale statistics used; original correct path retained |
| CP-010-C / REQ-010 | Static size 100/bound 2; admitted p95 3/bound 2; p95 2 exactly bound; unadmitted p95 1000 | Contradictions reject `contradictory-size-bound`; equality allowed; unadmitted values ignored. CP-GUARD-01–04 cover selector/explain only |
| CP-011-A / REQ-011 | Successful candidate plus rejected alternatives and fallback site | Explain matches compiler-emitted/visited plan, original/selected complexity, build/probe/output/memory and proof/profile identities |
| CP-011-B / REQ-011 | Deterministic distinct-key 1k/2k/4k/8k fixtures and separate all-equal joins | Per-engine differential output/trace plus measured counter exponent <=1.15; retain all four counts and output cardinality |
| CP-011-C / REQ-011 | Eligible and fallback cases, same-revision optimized/unoptimized builds, same machine/flags | At least five warm samples each; median wall <=1.10x, RSS <=1.20x, startup/request <=1.05x; cold startup recorded; no missing samples treated as zero |

### Executed lowering and evidence admission

An advisory `CollectionPlanDecision` or formatted explanation is insufficient.
The compiler must emit a plan identity tied to source/function/registry/target,
the produced MIR/artifact digest and the chosen blocks. Runtime instrumentation
must prove those blocks executed, including index build/probe and emitted rows.
The test compares against the unoptimized program, not a test-side reimplementation.
Do not infer hash/merge/fusion from elapsed time. Reject stale or substituted
receipts, mismatched artifact hashes, and receipts claiming a lowered plan when
the original loop executed. No production interface currently supplies this
complete contract, so CP-007/008/009/010/011 remain open where it is required.

Preserve the shared flow names: `prepare typed collection fixtures`, `compile
the same program in each engine`, `inspect the selected collection plan`,
`compare results and operation counts`. Reserve existing design helpers
`collection_fixture_path`, `run_collection_program`, `collection_plan_receipt`,
`assert_engine_parity`, `measure_collection_scaling` for actual production
connections. No silent/mock helpers were added. If a future helper is added
before implementation, it must fail explicitly and cannot qualify for PASS.

### TDD and current evidence boundary

CP-GUARD-01/02 describe a concrete baseline defect: a contradictory hard bound
can still admit Linear. CP-GUARD-03/04 protect valid-bound and stale-profile
behavior; CP-GUARD-05 checks semantic gates; CP-GUARD-06 exposes the current
memory-model limitation honestly. All six call the real selector and renderer.
These cases are authored but not runtime-verified: no admitted self-hosted
runtime has yet been found for this worktree. Static source analysis is not RED
or GREEN execution evidence. After runtime admission, execute the defect cases
against the recorded base and then the implementation once each, retaining
commands and results. Regenerate the manual with admitted docgen; the companion
manual is currently an authored inventory, not a generated/passing report.
