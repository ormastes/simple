# No-GC pointer and short-borrow hardening progress

## Evidence correction — 2026-10-21

**Earlier assertion-only native PASS claims below are withdrawn pending explicit
failure-guard requalification.** The schema input diagnostic printed zero bytes,
one source line and zero variants, yet continued past false `assert` checks and
exited 0. This affects assertion-based solver, NLL, binding, codec and HIR probe
acceptance evidence from the same producer. Compilation success remains valid;
zero exit plus a success print does not establish the stated assertions ran.
See `doc/08_tracking/bug/native_assert_no_failure_and_schema_empty_read_2026-10-21.md`.
New named guards call `exit(1)` explicitly; their negative control must pass first.

## Authority and scope

The existing plan is
[No-GC ownership recovery](nogc_ownership_recovery_plan_2026-10-19.md),
particularly §3.0–3.8, WP-01/02/03 and rollout Stage B. Pointer meanings come
from `doc/05_design/language/misc/memory.md`: `&T` unique, `*T` shared, `-T`
weak. Short borrowing is a synchronous non-retaining parameter effect, never
a stored/returned/captured/suspended reference. User direction on 2026-10-20
was to complete and harden this work before proceeding to Phase 3 and landing.

This is an appended implementation/evidence record. It does not replace
Claude's research or mark the entire recovery plan complete.

## Isolated session

- Owner: Codex, session `01a1587c-075a-76b1-90be-11902cebf865`.
- Worktree: `/home/yoon/dev/simple-nogc-short-borrow-completion`.
- Branch: `work/nogc-short-borrow-completion-20261020`.
- Target: `origin/release_phase3`.
- Base and fetched expected target: `d9e177de79ac599ecd4b165e39c26d99f037c357`.
- The existing dirty primary worktree and Claude's seed/lint worktrees were
  preserved; none of their unfinished changes were absorbed.

## Recovered progress

| Work | Evidence recovered | Current qualification |
|---|---|---|
| Seed sigil syntax/types | PR #4003 is in fetched history | Merged source; not runtime completion |
| Self-hosted parser/HIR/inference | PR #4011 is in fetched history | Merged source; foreign-kind boundary needed hardening |
| Seed moves and strict `any` | Saved `work/nogc-sigils-seed-moves`, commit `47c656c99ff`, plus four dirty review-fix files | Unfinished; no takeover edits made there |
| Sigil and `any` lints | Saved `work/nogc-sigils-lint`, head `a7be51aef77` | Local work; final review/execution not established here |
| Mandatory ownership facts on all routes | Baseline WP-00/01 documents bypasses | Open |
| Exactly-once drop, shared/weak runtime parity | Recovery WP-03 and sigil stages 2–3 | Open; parser/inference passes do not prove this |

## Hardening implemented in this session

1. **REQ-NOGC-FOREIGN-001:** A strict importer rejects ownership sigils from
   an unchecked or unavailable declaring module with `NOGC-FOREIGN-001` and
   an error type. Physical module surfaces retain the declaring strictness;
   aliases cannot upgrade it. Strict providers retain Unique/Shared/Weak;
   default importers retain Ref/Ptr/Infer.
2. Strictness participates in the semantic surface projection, invalidating
   dependent signatures when ownership meaning changes. Default-mode
   projection bytes retain their existing fold sequence. This does not yet
   qualify every HIR/object cache or introduce a runtime conversion API.
3. Parameter-effect analysis recognizes Unique/Shared/Weak HIR kinds.
   Unique parameters consume; shared and weak handles are explicit retainable
   handles, not short borrows. Foreign pointer/owner/reference contracts stay
   unknown. Wrapped pointee identity remains available for field analysis.
4. Summary decoding rejects malformed rows, unknown effects and duplicate
   functions atomically. Missing, invalid, ambiguous or foreign callee effects
   cannot advertise a short borrow for an argument or receiver. V1 summaries
   lack names, so named owner arguments are diagnosed rather than mapped to
   the wrong positional contract. Borrow-to-shared flow is not inferred safe.
5. Local signatures are seeded before the monotone inference fixpoint so a
   safe forward call does not retain a transient unknown-contract diagnostic.

The effect analysis remains advisory; these changes do not claim that it is
the mandatory ownership checker or that all existing name-based builtin
heuristics establish authoritative nonescape contracts.

## Regression scenarios and evidence

- `test/01_unit/compiler/frontend/nogc_sigil_import_contract_spec.spl`:
  legacy/strict providers, alias laundering, missing contracts, unchanged
  default mode, and semantic-identity separation.
- `test/01_unit/compiler/semantics/param_effects/param_effects_inference_spec.spl`:
  strict pointer effects, retained weak handles, foreign pointer contracts,
  invalid summaries, unknown callees/receivers, forward calls and named args.
- Independent read-only review identified weak-handle retention and unchecked
  method receivers; both received code changes and regression scenarios.
  The final scoped review found no additional concrete blocker. Compilation,
  executable assertions and runtime qualification remain unverified.
- `git diff --check`: passed before subsequent review edits; no executable
  semantic result is implied.
- Direct-env guards, `--working` and `--staged`: exit 0. The staged check
  examined an empty index; it is not a staged implementation qualification.
- **TEST_BLOCKED:** deployed
  `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  identifies itself as a Rust-built bootstrap seed. It was not used for the
  specs, docgen, compiler/core/MCP checks or release evidence.
- Older pure-Simple Stage 2 candidate (r14) hashes to
  `dad7e0ce61493f5e24ae21169b38e068eefcface6172bc3dbda289cc36de13c4`.
  Its provenance/sanity receipts were inspected, but current parent admission
  rejected its output path with `bootstrap-output-outside-allowlisted-root`.
  No allowlist override or descendant build was used to bypass that refusal.
- Latest recovered `s2r17.log` ends with
  `ABORTED: stage=stage2-compiler-tests exit=1` and explicitly says not to
  resume Stage 3 until the failure is understood. This record does not
  override that gate or claim a successful Phase 3.

## Remaining ordered gates

1. Obtain a currently admitted pure-Simple producer for the focused specs.
   Run the new import-contract spec and affected inference/front-end specs;
   keep diagnostic compiler evidence separate from general SPipe acceptance.
2. Resolve all remaining seed review fixes and lint review evidence in their
   respective isolated lanes. Reconcile semantics without overwriting them.
3. Implement/qualify mandatory ownership and short-borrow checking on native,
   interpreter and bootstrap routes, including CFG/loop/partial-move cases,
   escape/callback/suspension boundaries and explicit `any`/unsafe policy.
4. Qualify exactly-once cleanup, shared retain/release, weak upgrade and
   runtime-provider behavior. Fail unsupported safe routes closed.
5. Generate/review SPipe manuals with a qualified runner and run the required
   compiler/lib/MCP smoke checks. Obtain `STATUS: PASS` before integration.
6. Resolve the Stage 2 compiler-test failure manifest using the bootstrap
   owner's receipts, then use the canonical admitted Phase 3 resume path.
7. Refresh the exact target/head, run protected review/integration admission,
   and land only verified work. No protected branch or tag was moved here.

**Overall: incomplete; source hardening present, executable verification and
Phase 3/integration admission pending.**

## Continuation evidence: admitted compiler execution and recovered seed fixes

This section supersedes the earlier statement that no usable focused compiler
was admitted. It does not supersede the general SPipe/Phase 3 gates.

### Exact producer admission

The newer r17 producer was validated with the canonical
`produce-bootstrap-planner-admission-v2.shs --validate-parent-only` path.
The supported `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT` setting was bound to its
exact existing centralized output directory; no receipt, checker or admission
rule was modified. Validation exited 0 and rechecked the following bindings:

- Producer:
  `/home/yoon/dev/simple-lane-boot7/.simple/storage/build/bootstrap-r17/stage2/aarch64-unknown-linux-gnu/simple`.
- SHA-256:
  `29dd8539f3fe8e01df9b227e0621b20953fd736e239dafef8bafae8918abb3c2`.
- Stage: pure-Simple Stage 2; supported operation used: `native-build`.
- Admission: r17 `stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env`.
- Runtime snapshot:
  `a4274058240cd344a5b388f34981699559b257f6c0303fd479df893e950e65f3`.
- Evidence: `build/nogc-hardening/stage2-r17-admission.log`.

This validates focused diagnostic use. The Stage 2 compiler-test matrix still
failed; a Phase 3 resume has not been authorized by this focused probe.

### Native diagnostic results

`test/fixtures/compiler/nogc_effect_codec_probe.spl` was compiled using the
admitted producer and runtime, with isolated output/cache, a 900-second bound,
16 GiB memory cap and `SIMPLE_NO_STUB_FALLBACK=1`. The first invocation required
the supported cold SCV inventory initialization for this new worktree. With
that initialization, the actual nine-module closure compiled and linked:

- build exit 0; 75.14 seconds; peak RSS 3,389,504 KiB;
- generated native probe exit 0;
- positive valid-summary cases and negative malformed-summary cases executed;
- this is compiler diagnostic evidence, not general SPipe acceptance;
- the fixture's success-message wording was subsequently corrected without
  changing its assertions; it has not been rebuilt for that text-only edit.

The larger source-to-HIR diagnostic is
`test/fixtures/compiler/nogc_hir_contract_probe.spl`:

1. First build rejected the saved inference code's boolean parameter named
   `spawn` (`infer.spl:217`, native parser treats it as a keyword). The parameter
   was renamed to `spawns_task`; behavior is unchanged.
2. Second build completed parse/HIR/mono and attempted 314 MIR modules:
   297 succeeded, 17 failed. Build exit 1; 533.87 seconds; peak RSS
   4,303,728 KiB. Failures include enum payload typing, non-array iterable
   lowering and unresolved methods. Baseline parity of these dependency
   failures has not been established, so they are not labeled pre-existing.
   The probe's own unqualified `Error` pattern also failed; it is now qualified
   as `HirTypeKind.Error`, with an explicit `HirType` local. That correction
   remains unexecuted. Full HIR contract execution did not occur.

Logs are `build/nogc-hardening/effect-codec-build-cold-init.log`,
`effect-codec-run.log`, `hir-contract-build.log`,
`hir-contract-build-2.log` and `hir-contract-errors.json`. The bounded
verification/repair budget is exhausted; no unchanged build is retried.

### Seed recovery and bootstrap-only checks

The original Claude worktree was left unchanged. Its committed seed moves and
four dirty review-fix files were copied as patches into this owned feature
worktree, continuing the explicitly requested seed/pointer lane. The saved
patches are `build/nogc-hardening/saved-seed-moves.patch` and
`saved-seed-review-fixes.patch`.

Running the saved `simple-type` unit suite as a bootstrap-source check produced
138 passes and three failures: `any_in_traits_mixins_and_enums_rejected`,
`self_fields_are_owners`, and `loops_without_false_positives`. This did not run
the Rust seed as the normal Simple CLI.

Changes made after that evidence:

- Strict class method bodies are checked with a declaring typed `self`.
- Trait/mixin/enum annotations are included in the safe-`any` declaration scan.
- The two original annotation/class regressions passed (2/2 targeted tests).
- Independent review found missing implicit method-tail return validation.
  Function/method tails now share one macro-aware path and infer a move tail
  once. `method_and_function_tails_preserve_ownership` passed its explicit
  field, borrowed-tail, wrong-kind and valid-move controls (1 targeted test).
- A subsequently added recursive return guard rejects direct and aggregate
  short borrows even when the return type is inferred. Its new
  `short_borrows_do_not_escape_inferred_returns` regression is not yet run.
  Final read-only review found that lambda captures/bodies and match arm
  result types still produce fresh unknowns in the seed, so escapes hidden
  behind those forms can evade the typed guard. Complete these typed-result
  and nonescape checks (or fail unsupported strict forms closed) before
  claiming that inferred borrow escape is prevented generally.
- Mechanical extractions keep the expanded inference and checker files under
  the module-size limit: pure-Simple helpers moved to `param_effects/contracts.spl`,
  and unchanged seed item registration moved to `checker_items.rs`. Those
  final source edits have not yet been compiled.

The loop failure is still open. The required ownership-event CFG, including
backedges, exits, revival, scope-qualified places and short-loan boundaries,
is specified in
[`nogc_ownership_cfg_followup_2026-10-20.md`](../../../05_design/language/memory/nogc_ownership_cfg_followup_2026-10-20.md).
Do not replace it with a trailing-break or syntax-only exemption.

Native lifecycle inspection also confirms that current C `rt_unique_new`,
`rt_shared_new` and `rt_weak_upgrade` are identity operations with ownership
tracking explicitly absent (`src/runtime/runtime_native.c:18625` onward).
Self-hosted new-expression lowering still erases pointer construction to its
payload. Neither source typing nor the codec probe proves deterministic drop,
shared release or weak liveness. WP-02/03, general SPipe evidence, Phase 3
qualification and protected integration therefore remain incomplete.

**Continuation outcome: concrete source/test progress; not verify PASS, not
Phase 3, not landed.**

### Aggregate and match provenance hardening (continuation)

Strict match inference now retains arm result types and checks each owner
transfer once. The targeted `match_results_preserve_short_borrow_provenance`
and `match_owner_results_require_one_transfer_per_arm` tests passed. The same
run exposed missing tuple expression typing; direct inferred borrow returns
were rejected, but `(n, 1)` previously escaped through a fresh type variable.
Tuple and labeled-tuple inference now retains component types. Structural
transfer checking includes labeled tuple fields and nested labeled tuples.

Executed bootstrap-source diagnostic tests (not self-hosted or release proof):

- `short_borrows_do_not_escape_inferred_returns`: PASS, covering direct,
  explicit, tuple and array return forms after the tuple typing repair.
- `labeled_aggregates_preserve_ownership`: PASS, covering borrowed return,
  implicit unique-owner copy rejection and a valid explicit move.

Independent read-only review found tuple indexing still erased provenance.
Strict constant tuple indexing now returns the selected component type;
dynamic or out-of-range tuple indexing fails closed pending a typed selection
contract. Legacy indexing behavior is unchanged. The focused
`tuple_index_preserves_short_borrow` regression passed its borrowed-value
rejection and scalar-selection controls. `git diff --check` also passed.
Review found no additional obvious
blocker in the match/tail paths; this is not whole-checker qualification.

Logs: `build/nogc-hardening/seed-match-provenance-tests.log`,
`seed-aggregate-provenance-tests.log`, `seed-labeled-provenance-tests.log`,
and `seed-tuple-index-tests.log`. The original failed match/aggregate run is
retained as failure evidence. Do not erase it or count it as a full-suite pass.

Next implementation boundary remains the ownership-event CFG described above.
The existing pure-Simple `55.borrow/borrow_check` Place/BorrowGraph/NLL model
should be factored: it already records reads, moves and assignments, but
`moved_now` is source-order state and assignment revival is not retained as a
per-point event. Reuse those place overlap rules and CFG rather than add a
second incompatible ownership solver. Lambda checking, actual pointer
construction/drop/shared/weak lifecycle, native closure failures and the
required self-hosted/SPipe gates remain open. No completion or landing claim.

### MIR/NLL ownership fixed point (continuation)

Implemented `src/compiler/55.borrow/borrow_check/ownership_flow.spl`, reusing
BorrowGraph Place identities and overlap rules. It records ordered
Read/Move/Revive events, joins reachable predecessor facts by union, solves
backedges to convergence, and diagnoses reads only after convergence.
Definite writes revive covered descendants while preserving moved ancestors;
symbolic-index writes conservatively do not establish revival. Missing CFG
entry/targets, unmapped events, duplicate point IDs and work-budget exhaustion
are errors. Independent read-only review found the core transfer/worklist
monotone and identified the point-validation and array-snapshot gaps, both
addressed in source.

`nll.spl` now captures events at its existing use/move/assignment/borrow
recorder boundary and feeds the existing MIR CFG to the solver. It no longer
mutates BorrowGraph's linear `moved_now` state; standalone BorrowGraph users
retain their prior API. This is partial AC-OWN-04/05 implementation, not
typed-HIR or interpreter/native source-route parity.

Bounded native diagnostic evidence using the already admitted r17 producer:

| Cycle | Build | Execution |
|---|---|---|
| 1 | PASS, 4 modules, 83.06 s, 4,013,640 KiB RSS | Segfault: enum Place payload boxed as integer |
| 2 | PASS, 4 modules, 75.16 s, 4,056,940 KiB RSS | Same segfault despite explicit local type annotation |
| 3 | PASS, 4 modules, 74.36 s, 4,099,376 KiB RSS | PASS: typed-parameter insertion helper, full probe corpus |

The producer defect and GDB evidence are recorded in
`doc/08_tracking/bug/native_ownership_event_payload_boxing_2026-10-20.md`.
The passing corpus covers mutually exclusive moves; moved-state joins;
all-arm versus one-arm revival; repeated loop moves versus dominating refill;
break exits; continue paths bypassing revival; field/whole-local and symbolic
index behavior; same-point ordering; unreachable moves; malformed mappings;
and the work limit. It does not compile user ownership syntax end to end.

Passing snapshot:
`scv-revision-v1-6db5f8a745d6f9e0e052500902f133e2c9105e10946dd3cf479d7ff0ce34b5a3`.
Passing `ownership_flow.spl` SHA-256:
`c04c7a43ae184c865d4d96257f14f770782898c9d2c2cac821c9200976f04ebe`.
After this build snapshot, source added fresh output/merge arrays and copied
CFG statement points before appending terminators. These explicit snapshots
avoid depending on array alias behavior. The final solver SHA-256 is
`8eacce51b3074c95058efc9d2092313eba503c33d43b54a3de38f2a859b14d69`;
**those final edits are not covered by the passing executable**.

New executable sources:

- `test/fixtures/compiler/nogc_ownership_flow_probe.spl`: native solver corpus.
- `test/fixtures/compiler/nogc_nll_flow_probe.spl`: NLL recorder integration
  controls, not yet compiled/executed.
- `test/01_unit/compiler/borrow/ownership_flow_spec.spl`: six NLL unit scenarios,
  not yet executed under a qualified SPipe runner.

No further verify/fix attempt was made after the required three-cycle limit.
Next gate is final-source solver and NLL integration execution on an admitted
producer, followed by typed-HIR/source-route preservation and the remaining
WP-02/03 controls. The seed loop failure, lambda escapes, lifecycle operations,
full compiler closure failures and general qualification are still open.
**STATUS: incomplete; no verify PASS, Phase 3 admission, commit or landing.**

### Authorized final-source and NLL verification

The user resumed with `go` after the three-cycle escalation, authorizing the
requested additional bounded cycle. No passing checks were repeated without
a source or scope change: the final-source run covered the post-review copy
edits, and the NLL run covered the previously unexecuted recorder boundary.

Both native diagnostics passed with the same admitted r17 producer and
runtime authority recorded above:

| Diagnostic | Build | Run |
|---|---|---|
| Final ownership solver | 4 modules; 74.39 s; 4,141,560 KiB max RSS | exit 0, full branch/backedge/revival/projection/malformed-fact corpus |
| NLL recorder integration | 5 modules; 79.76 s; 4,184,024 KiB max RSS | exit 0, repeated move/refill/break/exit/branch/partial-move and block-storage-permutation controls |

Both compiled snapshots contain exactly the current solver source SHA-256
`8eacce51b3074c95058efc9d2092313eba503c33d43b54a3de38f2a859b14d69`
and NLL source SHA-256
`4cddffb8f8bdb678825f959e7302163d032cf71691ea9b1b1b5f5866e38b3a6a`.
Final solver snapshot:
`scv-revision-v1-86e1956774f5b41a2adc3ec35d77cec340b383afa4cd404c4021e114bd93006e`.
NLL snapshot:
`scv-revision-v1-b96fd79670f0a28ee05106886cddd3b3e24369c5ed43f0fb6347c81dabfc8587`.
Logs are `ownership-flow-final-build.log`, `ownership-flow-final-run.log`,
`nll-flow-build.log` and `nll-flow-run.log` under `build/nogc-hardening`.

Independent final source review found no remaining blocker in the scoped
array isolation, point validation, replay order or error conversion changes.
The native execution now covers those final edits. This supersedes the
earlier statement that final-source/NLL diagnostic execution was pending.
The std.spec unit file itself has not been run by a qualified SPipe runner;
the direct native fixture is not substituted for that release gate.

The compiler-artifact discovery still finds r17 as the latest local boot-lane
candidate; no newer admitted producer was found in those lanes. The prior
314-module HIR diagnostic still has 17 failing MIR modules and no established
baseline parity. Failures group into enum payload ownership/type recovery,
array iterable typing, unresolved methods, null-coalesce record ownership and
ambiguous enum cases. Its own qualified-Error fixture repair remains
unexecuted. Do not call these dependencies preexisting without a baseline
control. This broader compiler-closure gate, typed-HIR/source-route preservation,
seed loop/lambda checks, real pointer lifecycles and the remaining recovery
acceptance criteria still block whole-feature verify PASS and Phase 3/landing.

### 2026-10-21 — HIR binding payload repair and 20-job review

The updated direct native binding helper diagnostic built successfully in
203.51 s (5,149,596 KiB max RSS), then ran with exit 0. It checks unique,
shared and weak kind/nominal payload preservation, scalar payloads, optional
payload projection, untrusted expression attributes and concrete Let payloads.
Logs: `build/nogc-hardening/hir-binding-build-2.log` and
`hir-binding-run-2.log`. Helper source SHA-256:
`24ba686e015468620ee75416718e6fe372aee17ca9ca66de853f4974b2cc1a39`;
fixture SHA-256:
`07dcd76308a11b5cec47a2665e3935abd5619eca4f85374085307f4033bae069`.
This does not qualify the larger statement/match lowering callers.

The third bounded broader HIR diagnostic failed after 519.36 s, max RSS
4,528,872 KiB: 300/316 MIR modules succeeded and 16 failed. Snapshot:
`scv-revision-v1-9d42e486e9f667df12cec228aeeeb934a601b4ea43ee29546eddd53a3932f800`.
Log: `build/nogc-hardening/hir-contract-build-3.log`. No further identical
full-closure retry is authorized by this evidence. Failure counts are not a
baseline comparison, since the module closure changed.

The user requested 20 parallel jobs. A scoped implementation job repaired
optional projection after symbol lookup so symbol registration and Let payloads
use the same once-unwrapped resolution. This edit postdates the broader build
snapshot and remains native-unqualified. Read-only reviews identified:

- Generated match Field/Index and enum payload projections still lose known
  owner types; explicit statements provider import introduces an unqualified SCC.
- Plain Assign schema declares a concrete operator despite optional consumers;
  fix the schema consistently rather than invent a Set operator or weaken validation.
- Runtime owner constructors are identity hooks, new allocation kinds are erased,
  and backend Drop paths are no-ops; real pointer lifecycle remains absent.
- Short-borrow aggregate/store provenance, call-wide exclusive loans, captures
  and suspension boundaries are incomplete. Parameter-effect inference has no
  discovered production caller, and spelling-only builtin trust needs repair.
- CFG solver review found no concrete transfer soundness defect; adapter and
  source-route qualification remain separate open gates.

**STATUS: incomplete. No verify PASS, Phase 3 admission, commit or landing.**

#### Parallel review follow-up priorities

1. MIR adapter: CFG IDs currently use storage positions while terminators use
   explicit MIR IDs; call terminators revive both destinations before both
   edges. Missing Aggregate/Load/Store/GetField/SetField and arithmetic operand
   events prevent source-route coverage. Literal aggregate lowering also emits
   Copy operands without ownership-aware selection.
2. Effect checker: dictionary key retention omits `_flows_out`; unresolved
   receiver/callback builtin names are trusted; Unique parameter early return
   skips body diagnostics. Plain short-parameter escape cannot be accepted by
   changing the inferred interface to consume.
3. Loan checks: no call-wide overlap check, original boundary token or complete
   alias/store provenance; ownership fixpoint evidence does not establish a
   loan fixpoint. Await/Yield and capture facts are absent from the adapter.
4. Runtime reference warning from source review: bootstrap weak upgrade reads
   shared storage after final strong release frees it; do not copy that protocol.
   Pure Rc weak upgrade returns a payload after acquiring an unreleasable strong
   count; atomic upgrade needs a surviving control block and CAS protocol.
5. Test gaps: nested optional binder projection, real statement/symbol/match
   lowering, NLL record_borrow after move, constant-index overlap, and multi-block
   loop SCCs. No placeholder assertions found in the new native fixtures.
6. Integration: `scripts/check/land.shs` accepts main or release/*, not the
   planned release_phase3 spelling. No target/ref changes were made.

All read-only findings require normal implementation review and executable
qualification before acceptance. The 20-job review is not a verify PASS.

Additional strict-import blocker: legacy type aliases and generic defaults
expand via `type_aliases.spl` using importer strictness, bypassing the direct
NOGC-FOREIGN-001 guard. Expansion must validate the declaring alias owner.
Add legacy alias and generic-default negative controls before import contracts
can pass whole-route verification.

### User-authorized cache-preserving failed-module repair

The user requested continuing to completion using cache and manual failed-object
repair. Cache inspection found only frontend records in `hir-contract-cache`: the
failed MIR gate had emitted no native objects. Consequently, source repairs and
ordinary incremental rebuild are required; no object or cache identity was forged.
Producer/entry lineage is recorded in
`build/nogc-hardening/hir-contract-cache-lineage.json`.

Parallel source repairs now cover: optional Assign schema/transport and SVMG plain
writes; explicit async method provider and flattened bitfield presence flags; typed
array helper boundaries in dependency collection, cloning/substitution and semantic
fold generation; concrete HIR constructor owners and optional interpolation/yield
payloads; typed MIR call/intrinsic destinations; qualified optimization enums.
The combined diagnostic uses the existing cache and logs to
`hir-contract-build-4.log`. Its snapshot precedes subsequent alias/effect/CFG
repairs, so it cannot qualify those later edits.

Separately, native binding regression controls now include nested optional
projection and concrete plain/compound assignment payloads (`hir-binding-build-3.log`).
A native compiler-schema tool build (`schema-build.log`) was started to regenerate
artifacts rather than falsely claim generated schema freshness. All these new
checks are pending until their actual terminal results are recorded.

Later source edits still requiring execution: declaring-owner validation of alias
templates/defaults; dictionary-key escape analysis and method-identity trust; actual
MIR block/entry IDs and fail-closed malformed edges. New specs and a direct MIR CFG
identity fixture accompany these repairs. Independent review found further
spelling/summary trust issues; repair is in progress. No acceptance mark was changed.

Binding regression build 3 PASSED (208.95 s, 5,437,416 KiB max RSS);
run exit 0. This adds nested optional exactly-one-layer projection, unknown
optional attributes, and both absent/present Assign operator payloads. Logs:
`hir-binding-build-3.log`, `hir-binding-run-3.log`. Fixture SHA-256: `5623ea5ecc85113cb8c5ad8b1b7115f72b39fb1deb5d8c17fd57f7efc37954d2`.
This qualifies concrete payload transport only, not generated codec freshness
or the whole statement lowering closure. MIR CFG identity native probe is
running separately (`mir-cfg-build.log`); no PASS is inferred yet.

Broad repair build4 ended with 308/317 MIR modules successful, 9 failed,
570.11 s and 4,699,480 KiB max RSS; details in `hir-contract-errors-4.json`.
MIR CFG build1 failed on fixture Ret(nil) and misplaced Throw/Resume instruction
arms. Those were fixed; build2 compiled successfully (243.08 s, 5,905,700 KiB),
but its old assertion snapshot is not acceptance evidence. The guarded third
CFG fixture build is the bounded final replay for that criterion this cycle.

Cache audit correction: successful binding builds did retain91 native objects
and receipts per SCV scope. Different source snapshots select different complete
scopes because snapshot/revision digests are included in cache environment identity.
No missing cache flag was found; no identities/receipts were edited, no old objects
were substituted into a new world. This is conservative invalidation, not absent
object retention. Prelower-cache mode is explicitly unqualified and was not enabled.

### Current acceptance count and corrected executable evidence

The recovery plan contains44 distinct AC identifiers. The requested ownership/
short-borrow lane contains9: AC-OWN-01..05 and AC-BOR-01..04. All9 remain open
end to end; the other35 have not been verified by this session. Focused component
passes below must not be subtracted from whole-route acceptance counts.

| Guarded diagnostic | Build/run result | Evidence boundary |
|---|---|---|
| Explicit false-guard control | expected exit1, sentinel absent | proves named guard failure path |
| Ownership CFG, corrected projection constructors | PASS;146.52s,5,237,292KiB;run0 | graph/solver corpus, including owner/sibling immutability |
| NLL recorder | PASS;168.54s,5,012,608KiB;run0 | snapshot predates projection-constructor repair |
| MIR CFG identity | PASS;362.42s,6,683,884KiB;run0 | sparse/shuffled IDs, entry and malformed edges |
| HIR binding payloads | PASS;265.08s,5,801,004KiB;run0 | concrete owner/optional/Assign payloads only |
| Effect summary codec | PASS;139.57s,5,422,548KiB;run0 | malformed/valid summary corpus |
| Current assertion parser + typed lexer writeback | PASS;235.99s,6,183,076KiB;run0 | actual current parser source, separate false condition/message and rejected shapes |

These explicit-guard passes supersede earlier assertion-only claims only for the
specified source snapshots and scopes. Logs use `*-guarded-*`, plus
`assert-parser-build-2.log`/`assert-parser-run-2.log`, under build/nogc-hardening.
The original guarded solver failed because place_field/deref/index mutated their
input projection arrays; constructors now copy into a fresh array. Lexer writeback
also needed a typed parameter boundary: its old tuple-extracted record pointer was
boxed as an integer and multiplied by8 on retrieval.

The second broad repair cycle (build5) failed7/317 MIR modules after587.44s,
5,254,228KiB max RSS. Remaining diagnostics are saved in
`hir-contract-errors-5.json`; no broad HIR execution or verify PASS is claimed.

Schema input probe initially failed native codegen in fs._io_file_write_packed.
Replacing generic byte push with the checked existing packed-byte ABI fixed that
object; guarded build then passed172.38s/5,437,808KiB, but execution correctly
failed with `failed to open` for the existing HIR file. Disassembly confirms
rt_io_file_open expects(ptr,len,mode), while r17 caller supplied only(ptr,mode).
The pure text-extern registry has now been repaired to match the existing runtime
and Rust twin for open/exists/delete. Unchanged r17 cannot consume that source fix
until rebuilt. Generated codec/registry freshness remains blocked; no empty
generated artifacts were accepted.

**STATUS: incomplete;9 lane acceptance items remain. Phase3 and landing blocked.**

File-open root cause is now confirmed in native instructions, not speculative:
provider expects3 words while r17 emitted2. Pure registry repair and focused
`io_file_text_extern_spec.spl` are authored; source tests remain unexecuted by a
qualified runner. No native binary was patched or authority receipt rewritten.

The broad5 per-module diagnostic lines (aot:mir_errors:item, not the final
aggregated ERROR list) identify the7 failure owners exactly: hir_lowering.async;
expression_core; match_desugaring; union_narrow_arms; mir_opt.outline;
mir_opt._Inline.policy; mir_opt._OptimizationPasses.engine. The third bounded
repair batch targets these exact owners. HIR optional-bound symbols/expressions
now construct payloads behind concrete typed parameter helpers; inline destination
remapping uses LocalId?→LocalId? with concrete present-owner handling; outlining
preserves Span? without invalid coalesce-to-nil or empty-block indexing; optimizer
constant emission now uses concrete value/type parameters and typed map lookup.
The isolated optimizer probe is in native object compilation; no run PASS claimed.


### Parallel feature implementation — 2026-10-21 (not acceptance sign-off)

User requested implementation of unfinished features rather than additional audit-only jobs. Twenty implementation lanes produced source and substantive test changes: loan provenance and CFG liveness; production capture/suspension gates; checked short-call integration; aggregate, pattern and return ownership; strict-policy transport; bounded solver replay; unique move/drop; retained weak leases and scoped views; and Rc owned upgrades. Call-contract producer/transport integration is still in progress. New feature tests are authored, not yet executed. Earlier guarded component evidence predates these changes and does not qualify the new source.

The third bounded broad compiler repair attempt (`hir-contract-build-6.log`) compiled all 317 modules and reached linking, then failed on unresolved `compiler.hir.hir_lowering._Expressions.runtime_observation.hir_expr_runtime_discriminant`. Exit 1; elapsed 790.44s; maximum RSS 21,249,912 KiB. This is not a native-build PASS. Cache objects remain in place; no fourth broad rebuild is authorized by the local three-cycle rule. A source-only symbol resolution repair is assigned.

Open acceptance remains nine of nine core OWN/BOR IDs; the full plan contains 44 distinct IDs, of which the other 35 have not been audited by this session. Arc atomic nonzero acquisition, exceptional view cleanup, current schema/codec regeneration and qualified full CLI/SPipe evidence remain unresolved or unverified. No landing or release approval is implied.

#### Integration requirement correction

Plan §§3.0/3.3 distinguish parameter lending from storage transfer. Bare aggregate parameters (including Optional/tuple/array/dictionary containing Unique) default to short lending; only explicit outer Unique/Isolated consumes. Classification, effect inference and focused tests were corrected together. Move requirements for actual aggregate transfers remain independent.

Scoped scalar views now have a supported Result-returning callback API that invalidates the view before returning either Ok or Err. General exception unwinding is not qualified: the flat frontend does not construct the existing TryCatch representation and defer replay only covers return/falloff. See `doc/08_tracking/bug/lease_view_exception_cleanup_frontend_gap_2026-10-21.md`; this limitation does not close BOR-04.


#### Bounded 20-lane implementation file/test index — 2026-10-21

This index records authored implementation artifacts, not executed acceptance
results. Paths below are relative to the repository root. Parallel owners
retain their source boundaries; integration owns both pointer facades and the
existing parameter-effect oracle migration. No tests or native builds were run
while publishing this index.

| Lane | Implementation anchor | Test / diagnostic anchor |
|---|---|---|
| 01 Aggregate transfer | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | `test/01_unit/compiler/mir/nogc_struct_field_transfer_spec.spl` |
| 02 Loan overlap / mutation | `src/compiler/55.borrow/borrow_check/borrow_graph.spl` | `test/01_unit/compiler/borrow/loan_provenance_spec.spl` |
| 03 Short-call reentrancy | `src/compiler/55.borrow/borrow_check/call_loans.spl`, `nll_short_calls.spl` in the same directory | `test/01_unit/compiler/borrow/call_loans_spec.spl` |
| 04 Typed optimizer constants | `src/compiler/60.mir_opt/_OptimizationPasses/engine.spl` | `test/fixtures/compiler/nogc_optimizer_payload_probe.spl` |
| 05 Capture / suspension enforcement | `src/compiler/35.semantics/param_effects/short_escape.spl`, `src/compiler/80.driver/driver_hir_pipeline_support.spl` | `test/01_unit/compiler/semantics/param_effects/short_escape_spec.spl` |
| 06 Parameter contracts | `src/compiler/35.semantics/param_effects/contracts.spl`, `infer.spl`, `short_param_validation.spl` in the same directory | `test/01_unit/compiler/semantics/param_effects/param_effects_collection_contract_spec.spl` |
| 07 Facade / oracle integration | `src/lib/nogc_sync_mut/ptr/mod.spl`, `__init__.spl` in the same directory | migrated `test/01_unit/compiler/semantics/param_effects/param_effects_inference_spec.spl` |
| 08 Return ownership operands | `src/compiler/50.mir/_MirLowering/function_lowering.spl`, `src/compiler/50.mir/mir_lowering_stmts.spl` | `test/01_unit/compiler/mir/ownership_return_operand_spec.spl` |
| 09 Pattern projection types | `src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl` | `test/01_unit/compiler/hir/nogc_match_projection_spec.spl` |
| 10 Fresh lease views | `src/lib/nogc_sync_mut/ptr/lease.spl` | `test/01_unit/lib/ptr/lease_spec.spl`, `test/fixtures/compiler/nogc_lease_view_probe.spl` |
| 11 NLL CFG / provenance | `src/compiler/55.borrow/borrow_check/nll.spl` | `test/01_unit/compiler/borrow/nll_loan_cfg_spec.spl`, `short_local_provenance_spec.spl` in the same directory |
| 12 Inferred binding / array ownership | `src/compiler/20.hir/hir_lowering/binding_types.spl`, `_Expressions/expression_components.spl` under the same lowering root | `test/fixtures/compiler/nogc_hir_binding_type_probe.spl`, `nogc_aggregate_transfer_probe.spl` in the same directory |
| 13 Call-contract producer / transport | `src/compiler/50.mir/_MirLowering/short_call_contracts.spl`, `src/compiler/50.mir/mir_data.spl` | `test/fixtures/compiler/nogc_mir_call_loans_probe.spl` |
| 14 Strict policy transport | `src/compiler/20.hir/hir_types.spl`, `hir_lowering/_Items/module_build.spl` under the same HIR root, `src/compiler/50.mir/_MirLowering/module_lowering.spl` | `test/01_unit/compiler/semantics/param_effects/driver_nogc_param_effect_gate_spec.spl` |
| 15 Canonical ownership predicates | `src/compiler/20.hir/ownership_types.spl` | `test/01_unit/compiler/borrow/ownership_types_spec.spl` |
| 16 Typed lexer slot updates | `src/compiler/10.frontend/core/lexer.spl` | producer repair; no standalone new test or qualification claimed |
| 17 MIR / CFG borrow bridge | `src/compiler/55.borrow/borrow_check/mod.spl`, `src/compiler/50.mir/mir_instruction_graph.spl` | `test/01_unit/compiler/borrow/mir_adapter_spec.spl`, `test/fixtures/compiler/nogc_mir_cfg_identity_probe.spl` |
| 18 Retained Rc upgrades | `src/lib/nogc_sync_mut/rc.spl`, `src/lib/nogc_async_mut/rc.spl` | `test/01_unit/lib/nogc_sync_mut/rc_weak_owner_spec.spl`, async counterpart under `test/01_unit/lib/nogc_async_mut/` |
| 19 Unique lifecycle | `src/lib/nogc_sync_mut/ptr/unique.spl` | `test/01_unit/lib/nogc_sync_mut/unique_lifecycle_spec.spl`, `test/fixtures/compiler/nogc_unique_lifecycle_probe.spl` |
| 20 Owned weak acquisitions | `src/lib/nogc_sync_mut/ptr/weak.spl` | `test/01_unit/lib/nogc_sync_mut/weak_owned_lease_spec.spl`, `test/fixtures/compiler/nogc_weak_owned_lease_probe.spl` |

Both pointer facades now expose `unique_try_get`, `unique_drop`,
`unique_release`, `WeakLease`, `weak_upgrade_owned`, `weak_lease_value`,
`weak_lease_release`, `LeaseView`, `lease_acquire`, `lease_release`,
`lease_with_view`, `lease_with_view_result`, and `lease_view_read`. The lease
owner confirmed the result-callback API is
`(WeakLease, fn(LeaseView) -> Result<i64, text>) -> Result<i64, text>`.
It closes its view epoch before returning either result branch. This source
contract does not establish exception-unwind or asynchronous callback safety.

The new unique, owned-weak and lease-view native feature probes use explicit
exit-backed guards and remain unrun for this implementation round. The current
aggregate-transfer and MIR-call-loan feature edits likewise require fresh
qualified execution; earlier guarded component results cannot qualify them.
Unit/spec files in this index are authored and unrun by a qualified SPipe runner.
Scoped whitespace and export-name checks are source checks only.

All nine core criteria remain OPEN: **AC-OWN-01, AC-OWN-02, AC-OWN-03,
AC-OWN-04, AC-OWN-05, AC-BOR-01, AC-BOR-02, AC-BOR-03, AC-BOR-04**.
Remaining plan criteria, codec/schema freshness, current producer admission,
actual native execution, full CLI/SPipe checks and landing gates are not waived.
**STATUS: implementation advanced; no acceptance PASS, Phase 3 or landing.**

#### Final source barrier and qualification scope

Production driver admission, exact checked-contract transport, actual MIR call checking, result-provenance union, canonical reborrow origins, and optional optimizer safeguards are source-complete at the current barrier. Targeted new native builds are running for unique lifetime, owned weak leases, recoverable scoped views, actual MIR adapter events and actual call loans. Their outcomes must be recorded separately; no build result is implied here. Both working and staged direct-env-runtime audits returned PASS after the parallel changes.

The short boundary is a static compositional scope token justified by checked non-retention/no-escape, not a runtime caller token transported across activations. Liveness is point-level over local roots; projected alias identities are preserved, but unrelated live fields can conservatively extend loans. Full field-sensitive liveness, compiler heap lifecycle, Arc atomic nonzero acquisition and qualified schema/cache evidence remain open.


#### Bounded feature-probe evidence update — 2026-10-21

Two native guarded-library probes completed successfully. The unique lifecycle
build exited 0 in 142.08 s with max RSS 5,466,720 KB; its run log reports move,
reuse, reset, negative-payload handling, and exactly-once release passed. The
owned weak-lease build exited 0 in 164.92 s with max RSS 5,499,832 KB; its run
log reports retained lifetime, expiration, reset generations, and one-time
release passed. These are component probe results only and do not close any
acceptance criterion.

The first lease-view native build failed because its fixture had unresolved
module initializer types at lines 6:18 and 8:22. Explicit type annotations
were added; lease-view build 2 is currently running. The first MIR adapter and
MIR call-loan builds both failed at `nll.spl:350:35` with a parser error
(expected `>`, got `]`); the source parse issue was fixed, and both build-2
sessions are currently running. The first-build aggregate HIR failures were
consequences of that parser failure, with worker publication blocked. No run
result is yet recorded for lease-view, adapter, or call-loan probes.

All nine core acceptance criteria remain OPEN. The known conservative
whole-parent join still rejects a valid disjoint-field positive case; that
authored positive case has not run. Arc CAS qualification, schema/codec
regeneration, and exceptional-unwind qualification remain open. These bounded
probe outcomes do not establish acceptance PASS, Phase 3, or landing.


Lease-view qualification completed after the prior snapshot: native build 2
exited 0 in 141.09 s with max RSS 5,777,552 KB. Its run log reports retained
lifetime, repeated views, escape, reentrancy, release, reset, and recoverable
callback errors passed. This remains component-probe evidence, not acceptance
closure.

At the latest bounded log snapshot, adapter build 2 had completed its main
build/weave phases and was entering native-cache work; call-loan build 2 was
still in MIR lowering (50/132 modules). Neither had a terminal result or run
log at this snapshot.

The reproducibility manifest for the three terminal native library probe build/run pairs is `build/nogc-hardening/parallel-feature-evidence.json`. It records probe binary and fixture SHA-256 values, producer identity, log paths, exits, and build metrics; it does not sign off acceptance criteria.

The call-loan build-2 failure was isolated to the probe fixture constructor at
`test/fixtures/compiler/nogc_mir_call_loans_probe.spl:34`: its `CallTerminator`
passed `nil` for the optional `unwindBlockId` and following optional fields. The
native bootstrap rejected those payloads because this constructor requires
`None` for closed optional values. The fixture now uses `None` in those three
slots. This records a fixture correction only; it does not establish a compiler
fix or call-loan probe result. The same-cache final build/run is pending.

MIR adapter qualification update: adapter build 2 published its native binary
and exited 0 (259.81 s, max RSS 6,554,700 KB), but run 2 segfaulted under the 30-second timeout guard and exited 139
(see `build/nogc-hardening/mir_adapter-feature-run-2.log`; no timeout occurred).
The process exited after about 0.98 s. The captured debugger trace repeatedly enters
`compiler.borrow.borrow_check.ownership_flow.ownership_write_covers`; the
register/disassembly log shows the fault at a load within that function. A
successful build therefore does not qualify the runtime probe. The adapter
acceptance remains open pending a bounded source repair and fresh qualification.
The three-library manifest remains limited to the unique, weak-lease, and
lease-view probe pairs.

Final bounded feature-probe cycle update (2026-10-21): adapter build 3 and
call-loan build 3 compiled and published their native probes, but runtime
qualification failed for both. Adapter run 3 segfaulted in
`ownership_flow.ownership_write_covers` (exit 139 under the 30-second guard);
call-loan run 3 segfaulted in `__GI_strcmp` → `rt_text_eq_any` →
`NLLChecker.check_short_call` (exit 139). The latter's typed mode binding is a
local candidate only; the three-cycle cap is reached, so no further native
probe is claimed. See
`doc/08_tracking/bug/native_short_call_mode_array_text_conversion_2026-10-21.md`.
The only successful build-and-run component probes in the manifest remain the
unique lifecycle, owned weak lease, and lease-view probes.

Read-only GitHub inspection found repository `ormastes/simple`, default branch
`main`, no PR with head `work/nogc-short-borrow-completion-20261020`, and no
remote ref for that work branch. Queried refs were main
`c8b4a86ab6876ecb825b4ea42b2c01d388b23a95` and release_phase3
`471ccc083397fb17812ba43459b233e7cd3dfde2`. The five most recent workflow
runs were on `release_phase3` or `work/root-critical-enum-extension-20261021`
(skipped/failing); none provides CI evidence for this lane.

All nine core acceptance criteria remain OPEN; these component results and
source candidates do not establish acceptance PASS, Phase 3, or landing.

#### Nine-criterion implementation batch status — 2026-10-21

This is a source-progress snapshot from the assigned criterion owners. “Done”
means the owner reports the scoped implementation change is present; it does not
mean acceptance is verified. No tests or builds were run for this batch. The
four earlier successful component probes predate this batch and do not verify
these changes.

| Criterion | Current source-progress status |
|---|---|
| AC-OWN-01 | In progress: strict owner moves and short aliases |
| AC-OWN-02 | In progress: hidden struct-parameter copy |
| AC-OWN-03 | Enum/optional/Result transfers reported done; `.push()` transfer remains in progress |
| AC-OWN-04 | CFG scenario additions reported done |
| AC-OWN-05 | Unreachable-path adapters reported done |
| AC-BOR-01 | Projection provenance reported done |
| AC-BOR-02 | Five capture/suspension fixes reported done |
| AC-BOR-03 | Origin-only loan graph reported done; NLL integration in progress |
| AC-BOR-04 | Compiler-static contract gap documented and open |

All nine criteria remain unverified and open for acceptance. No PASS, Phase 3,
or landing claim follows from this progress snapshot.

### Nine-criterion implementation batch — final source handoff

AC-OWN-01 live binding/reassignment now consult actual strict ownership policy, bypass owning struct/array clones, and preserve short aliases in distinct locals with original provenance. AC-OWN-02 strict struct/trait parameters avoid hidden defensive copies. AC-OWN-03 enum/optional/result payloads, dictionary key/value insertion, push and map-result insertion select ownership transfers before erased runtime storage; container receivers remain copies. AC-OWN-04 gained branch-order, early-return and multi-block refill scenarios. AC-OWN-05 suppresses eager diagnostics in unreachable blocks while retaining global CFG validation.

AC-BOR-01 preserves non-scalar field/index provenance through aliases and escapes. AC-BOR-02 covers borrowed callback results, explicit captures after suspension, nested suspension, async parameter capture and while-condition backedges. AC-BOR-03 adds actual-view versus inherited-origin metadata; graph copy/dedup and NLL propagation preserve both CFG alternatives. Independent graph-owner source review found no further concrete blocker in the combined implementation. These are source-review findings, not execution evidence.

AC-BOR-04 remains an implementation gap: checked nonescaping callback contracts and compiler fresh borrow regions are absent; see `doc/08_tracking/bug/owned_lease_short_view_static_contract_gap_2026-10-21.md`. Arc acquisition, runtime cleanup and current generated schema/codec admission also remain unresolved or unverified.

No builds/tests were run for this batch because the session three-cycle cap is exhausted. The four prior passing guarded native probes predate these edits and do not qualify current source. All nine core acceptance IDs remain OPEN; Phase 3 and landing are not approved. Smaller-model evidence triage/documentation was reviewed by the parent; substantive ownership changes received parent and/or independent source review.

AC-BOR-04 source update — local callback-contract checks are now implemented
in `callback_contracts.spl` and consumed by `infer.spl`/`short_escape.spl` for
ordinary Call and StaticCall callback slots, named arguments, and fail-closed
unknown imports. The transient PeCtx table preserves admitted symbol/slot
contracts for one analysis/reporting pass. Duplicate-symbol fail-closed repair
is in review. This supplies local nonescape proof source progress only and is
unverified. Fresh lease-view region binding, trusted imported/reexported
contract receipts, actual object retention, and compiler lifecycle cleanup
remain open. AC-BOR-04 stays OPEN; no tests/builds were run for this update, and
the earlier four probe passes predate it. See
`doc/08_tracking/bug/owned_lease_short_view_static_contract_gap_2026-10-21.md`.

### Verification handoff freeze

Current modified compiler/library/spec source hashes are recorded in `build/nogc-hardening/current-source-verification-handoff.json`. This inventory includes the isolated lane changes; it is not a reviewed commit manifest or evidence of acceptance. Local callback proof duplicate-symbol and symbol-owner hardening was completed and parent-reviewed after the earlier table. Fresh regions, trusted imported receipts, lifecycle/drop qualification and atomic Arc acquisition remain open. The three-cycle limit is exhausted; a fresh scoped verification session must validate the recorded current source before Phase 3 or landing. No fourth build was run and no requirement was marked complete.

### Astra shared-blocker review and parallel missing-feature implementation

User requested isolated landing of fixes that unblock other agents, with Astra review. Independent Astra review selected `src/compiler/50.mir/text_extern_abi.spl` plus `test/01_unit/compiler/mir/io_file_text_extern_spec.spl` and a focused ABI evidence note as a separable candidate: open(path,mode) must expand to (ptr,len,mode), exists/delete(path) to (ptr,len). Source verdict supports correctness; LANDING VERDICT: REQUEST CHANGES. Existing r17 and defect evidence do not execute the edited table. Required evidence is a qualified isolated producer, registry/spec execution, real guarded open/read/write-or-append/exists/delete/missing-file/raw-expanded fixture, and applicable compiler/core/MCP gates. No landing or push occurred. An isolated extraction is being prepared without tests/builds.

Parallel implementation now includes explicit-owner fresh callback-region proof (all direct invocations validated), fresh lambda-region consumer integration, and trusted imported callback receipts using actual resolver-terminal provider identities. These remain source work, unqualified. Arc cannot safely acquire owners through the existing incompatible providers; no unsupported API/provider was fabricated. General Drop lacks persisted owned/destructor identity; blanket no-op-to-error conversion was rejected because scalar marker drops can be legitimate. Astra recommends explicit no-cleanup/known-cleanup/unresolved classification, with unresolved owned cleanup rejected; a default false drop-required flag is insufficient.

### Astra BOR-04 review: REQUEST CHANGES

Astra found three blocking gaps in fresh-region source proof: mutable/overlapping owner arguments were not distinguished by position-only receipts; actual indirect MIR calls do not receive checked owner/mode/invocation evidence from the HIR table; lambda parameter identities lacked module/global symbol authority. Producer/consumer hardening is being applied fail-closed, but none of these source edits are executed or accepted. The exact missing per-invocation transport is designed in `doc/05_design/language/memory/checked_callback_invocation_transport_2026-10-21.md`; its implementation, NLL extent handling, optimizer remapping and schema admission remain pending.

Imported synchronous callback receipts now use actual resolver-terminal owner metadata, live checked providers, complete function body digests and restricted canonical signatures. Provider transactions stage without partial publication and defer only dedicated pending-import diagnostics with resolver identity; generic local errors remain fatal. Structured pending-call diagnostics are finishing integration. Imported fresh-region receipts remain unsupported. No broader trust is inferred from these narrow receipts.

The independent file-I/O ABI fix is extracted to `/home/yoon/dev/simple-io-file-abi-review-20261021` at base `d9e177de79ac599ecd4b165e39c26d99f037c357`, containing only the table change, focused spec and qualification note. Astra requests actual updated-producer execution and applicable gates before landing. No commit, push, fourth build cycle, Phase 3 approval or acceptance closure occurred.

### User-authorized limit increase: 10 cycles

User explicitly authorized increasing the verify/fix limit to ten and continuing. Existing attempts are retained, not renumbered or reset. `build/nogc-hardening/verification-cycle-ledger.json` records three completed ownership cycles and cycle four started against current source, with separate existing caches for actual call loans, NLL flow and ownership flow. Source is frozen during snapshot admission. Prior green probes are not rerun without changed-source justification. Shared-blocker ABI landing still requires Astra-requested producer and behavior evidence; user authorization does not turn source review into a runtime PASS.

### Authorized verification progress

Current-source guarded NLL flow and ownership-flow probes compiled and executed successfully (167.57s / 6,580,112 KiB and 189.22s / 6,552,364 KiB). The actual-MIR call-loan probe passed on attempt six (275.33s / 7,596,976 KiB), including valid shared forwarding and negative alias/boundary/contract/return controls. Typed producer boundaries corrected text-key and mode-value boxing; checks were not disabled. These are scoped component receipts, not full acceptance closures.

HIR contract attempt seven compiled all 324 modules and linked (828.28s / 23,781,484 KiB), then rejected an obsolete fixture expectation that plain short parameters become consuming when stored. Attempt eight uses paired explicit-owner insertion, short-borrow rejection and use-after-insertion diagnostics, with parser/lowering prerequisite guards. Isolated ABI attempt two uses the focused codegen import and remains live. All source/caches and failed receipts are preserved.


### 2026-10-21: user raises repair cap to 10; diagnostic boundaries

The user explicitly raised the repair limit to ten attempts per lane. Existing successful checks remain trusted and historical attempt numbers remain intact.

The selected native classifier runner diagnostic (attempt 3, verbose with retained artifacts) captured the actual compiler argv. A direct child replay failed immediately with stdout `Error: unknown option: --refresh-source-authority` and empty stderr. r17 therefore cannot satisfy this runner authority contract. The authority flag stays enabled; the runner must expose stdout and process limits rather than hide the cause. Evidence: `build/nogc-hardening/test_runner-classifier-native-diagnostic-3.log` and `runner-child-direct-diagnostic-3.log`.

A separate two-worker MIR diagnostic built successfully in 210.41 seconds, but both MIR workers rejected the lane as unsupported. Its receipt records zero completed MIR workers, three worker/ledger failures, and `outcome=fallback`, `all_stopped=true`. The emitted binary used serial MIR. This does **not** qualify MIR sharding or a parallel full CLI build; no repeated serial behavior check was run. Evidence: `build/nogc-hardening/nll-flow-sharded-build-1.log`.

Acceptance remains open; no landing or push has occurred.


### Full CLI HIR blocker: imported callback receipt constructor qualification

The full CLI cache reported one HIR fatal in `src/compiler/35.semantics/param_effects/imported_callback_receipts.spl:55:31`: `unresolved name: Function`. The constructor belongs to `HirTypeKind` (the same file pattern-matches it as `HirTypeKind.Function`), but the synthesized signature used unqualified `Function(...)`. The source now qualifies that constructor as `HirTypeKind.Function(...)`; this is a narrow name-resolution correction, not evidence of successful full-CLI compilation. Root will reuse the admitted cache for the next attempt. No acceptance status changes until that attempt terminates.


### 2026-10-21: qualified diagnostic outcomes before next source barrier

HIR contract attempt 9 built successfully (889.16 seconds, 31,163,532 KiB peak RSS), but its guarded execution segfaulted (139). GDB locates the failure in `ModuleSurfaceBuilder.add_parsed_canonical`; disassembly shows the caller converting a parser-module record through `rt_value_as_int_wide` after discarding an unwrap result. The repeated stack frames are not evidence of source recursion. A concrete typed dictionary lookup repair is under review before the final allowed attempt 10. No HIR acceptance PASS is claimed.

Full CLI qualification attempt 2 failed at the HIR aggregate gate after 1,408.85 seconds (9,623,140 KiB peak RSS). Exactly one terminal module failed: `compiler.semantics.param_effects.imported_callback_receipts`. Its fatal diagnostic is `unresolved name: Function` at line 55, an unqualified enum constructor in the newly implemented receipt producer. No artifact was published.

The isolated ABI harness attempt 3 exposes closure-wide MIR baseline errors, including enum exhaustiveness, constructor payload types and unresolved methods. Some fixes already exist in the completion lane but are absent from the isolated base. Keep the eleven-line ABI table candidate separate from these compiler prerequisites; this execution cannot establish ABI correctness.


### Native runner generated-source staging corruption

A retained native diagnostic stage for `ownership_types_spec.spl` is 4,095 bytes with a binary prefix, while its input is the expected 7,980-byte Simple source beginning `# @req AC-OWN-03`; their SHA-256 digests differ. The stager reads `[u8]` then forwards it to `file_write_bytes`, whose native provider has explicit pointer/length arguments. The prefix resembles array metadata, but the exact faulty boundary is unproven. Evidence and the retained artifact are recorded in `doc/08_tracking/bug/native_test_source_stage_bytes_corruption_2026-10-21.md`. Native runner qualification remains blocked; this is not a compiler/provider fix or acceptance PASS.


### 2026-10-21: runner failure reporting regression confirmed

The reviewed runner reporting change compiled in attempt 3 (422.13 seconds, 13,623,488 KiB peak RSS). Its selected native classifier run still failed before the spec executed, but now correctly reports `exit=1, limit=, budget=pass, completion=unavailable` and stdout `Error: unknown option: --refresh-source-authority`. The failure verdict and authority requirement are preserved. This verifies the stdout-loss regression only; present-receipt serialization and 4096-unit truncation boundary controls remain unverified, as do mandatory core/MCP gates. Logs: `test_runner-qualification-build-3.log`, `test_runner-classifier-native-3.log`. No landing approval.

Disassembly of the prior runner additionally establishes a byte-write ABI mismatch: the Simple facade passes the array handle as `x2` without initializing a data length in `x3`, while the raw C provider consumes a pointer/length pair. The selected immutable runtime archive exports the tagged-value `rt_file_write_bytes_array` adapter. Astra approved a guarded alias design in principle: exact authoritative extern `(text,[u8])->bool`, two semantic arguments, boxed text at position zero, no pointer/length expansion, and unchanged raw four-word/local/qualified homonym calls. A separate pure-Simple source repair is in progress and unverified.


### 2026-10-21: HIR lane reaches the user-authorized ten-attempt cap

Attempt 10 built in 864.14 seconds (35,489,488 KiB peak RSS), then the guarded executable segfaulted with exit 139. GDB now identifies `lib.common.crypto.sha256.Sha256StreamV1.update`; this is beyond the previous registry transport crash, but not a passing HIR contract result. Evidence: `hir-contract-build-10.log`, `hir-contract-run-10.log`, `hir-contract-gdb-10.log`. No attempt 11 is authorized under the current cap; stop this lane and report the remaining failure. Other independent running builds and source reviews retain their own historical counters.


### 2026-10-21: explicit user continuation for manual object repair and local redeployment

The user explicitly requested failed-object manual compilation until passing, the ABI repair, and then local pure-Simple redeployment. Work resumes on these concrete prerequisites; the previous ten-attempt HIR failure remains preserved, with no fabricated PASS. The older full CLI attempt 3 timed out (124), produced no candidate, and left an exact-cache orphan worker. That worker was stopped; a later process check found it absent. Existing caches and all failure receipts were preserved.

Manual ABI-table object compilation succeeded: 227.49 seconds, 6,711,504 KiB peak RSS, 3,001,888-byte ELF ET_REL object. This is object-compile evidence only. Manual module lowering still failed at the source-spanned `enum_variant_payload_arity` optional-array binding (`module_lowering.spl:913`). That lookup and its sibling type accessor now use explicit `[HirType]` values after membership checks. Grouped diagnostics include nonfatal collision advisories as well as real errors; do not mass-add wildcard arms or treat every message as a new fatal.

Small-model triage found real missing Throw/Resume consumer cases; source fixes now retain both exception operands while treating both terminators as terminal CFG nodes. Surviving CompleteRegion/DynRegion/TypeTest patterns now record the existing specified fatal codes before diagnostic-only recovery. These source changes remain unexecuted and await review.

The byte-write qualification exposed two further defects: generic tagged slots are truncated by the C `_array` writer, and typed-array-to-Any lowering reconstructs packed arrays as generic arrays. The pure-Simple facade now keeps allocator results as Any and owns explicit scratch cleanup. A validated runtime-value entry is being split from the typed wrapper so packed handles can be passed unchanged and tested directly. No C/Rust edits or nonexistent identity provider were added. Native ABI correctness and redeployment are still unverified.


### Pure-Simple local redeploy repair continuation

User explicitly requested local pure-Simple repair followed by redeployment. Frozen diagnostic source: `/home/yoon/dev/simple-pure-redeploy-20261021`; revised bridge snapshot: `/home/yoon/dev/simple-pure-redeploy-v2-20261021`. Neither is deployed.

- Native byte facade probe 4 built successfully (140.29s, 3,944,636 KiB max RSS), then failed `typed packed-readback source write`. Receipt and retained output: first snapshot `build/nogc-hardening/file-bytes-facade-run-4.json`, `/tmp/simple-byte-write-v4-d2assxf6`. Existing generic-input PASS is unchanged.
- Source repair inspects typed packed backing before erasure and copies it through the existing `rt_bytes_from_raw` provider with an Any return, preserving its packed allocation. It frees only this owned copy after synchronous writing. Astra approved this bounded design for qualification. Probe 5 is running; no PASS claimed.
- Focused manual object for `20.hir/generated/hir_children.spl` failed with six constructor errors (163.64s). Trace: four expected named#32, two named#51; all remembered/source type none. This is fresh type-provenance evidence, not a stale-cache conclusion. Incorrect initial non-generated entry attempt was terminated, then corrected explicitly.
- Canonical new-source Stage 2 refresh launched from revised snapshot using admitted pure-Simple r17 parent, separate output `build/bootstrap-pure-redeploy`; no Rust seed or old-output mutation. Build, admission, full CLI qualification and deployment remain pending.

Native facade probe 5 PASS (binary SHA f7fa5661a97c507b3c848ed608fd2ad4166af2ee64ca2198ecac28b61d3e070d): exact generic and typed packed-readback bytes, preserved source, invalid-input rejection and failure behavior. Receipt in revised snapshot `build/nogc-hardening/byte-write-facade-native-receipt-5.json`. Shared compiler-copy fix is separately source-reviewed by Astra, still unexecuted. Canonical refresh attempt 1 failed LLVM discovery; attempt 2 pinned existing LLVM23.1.2 successfully and then rejected absolute plugin/composition source selectors at entry-closure-root validation, before parsing. Correct root-owner scripts rather than weakening the receipt validator.

Astra subsequently approved the source-driven U8 copy repair and exact Any-boundary regression; native execution of the rebuilt compiler remains pending. Approved launcher correction verifies fixed checkout roots physically before passing logical relative selectors, preserving source order and receipt checks. Final production snapshot `/home/yoon/dev/simple-pure-redeploy-v3-20261021` binds 165 input paths in `build/nogc-hardening/frozen-source-manifest.json`. Manual hir_children object attempt 3 and canonical Stage 2 refresh attempt 3 are running there. The separate v2 test-runner attempt 5 is also building to verify actual source staging with the native-qualified facade. No deployed binary, release or acceptance closure claimed.

Manual failed-object repair milestone: `manual-hir-children-build-3.log` in frozen v3 finished PASS, exit0, 219.57s, 5,421,360 KiB max RSS. Artifact `build/nogc-hardening/manual-hir-children.o` is retained with ELF/type/hash receipt. Six prior fatal constructor mismatches are gone without weakening validation. This qualifies the generated-source bootstrap compatibility correction; the new compiler metadata helper still needs execution by a rebuilt producer. Canonical Stage2 and revised runner builds remain active.

Actual runner staging qualification PASS: revised v2 runner attempt5 built exit0 (395.94s,15,370,044KiB maxRSS), then ownership_types_spec staging produced exactly7,980bytes and SHA cf5f004cc8950125fcaacc383fb3bf698958de65825f464d09337ddc1dfb54a7, identical to original. Retained stage and receipt are v2 `build/nogc-hardening/native-staging-artifact-5/entry.spl` and `native-staging-receipt-5.json`. This repairs actual source-staging ABI corruption. Selected spec remains NOT_EXECUTED: r17 child rejects required --refresh-source-authority; Results1total0passed1failed is failure evidence, not acceptance PASS. Replacement canonical compiler build remains active.

Generator equivalence attempt3 FAIL despite exit0: updated native generator built successfully (180.37s,4,638,024KiB), but emitted only4,385bytes versus checked-in56,367bytes, reported0variants for bothAST/HIR. Temporary outputs retained `/tmp/simple-hir-generator-parity-ms4votcw`; receipt frozenv3 `build/nogc-hardening/hir-generator-parity-3.json`. No generated source overwritten. This is a vacuous generation failure requiring schema loading/parsing diagnosis; typed annotations remain object-qualified but generator equivalence is not qualified.

### Struct-carrier guard probe: generic helper link failure

The first isolated native build of `test/fixtures/compiler/nogc_struct_carrier_guard_probe.spl` failed at LLVM link time; retained log: `build/nogc-hardening/struct-carrier-guard-build-1.log`. Primary diagnostic: `ld.lld: error: undefined symbol: ...nogc_struct_carrier_guard_probe.carrier_absent`. The generic Simple helper was not linked with a matching specialization. The fixture now has separate `LocalId` and `MirOperand` helper functions with the same classifier logic, avoiding that generic helper call while preserving both carrier cases. This is a fixture diagnostic adjustment only: the generic extern declarations remain, no product guard was edited, and the revised probe awaits root-owned qualification. See `doc/08_tracking/bug/native_generic_simple_helper_specialization_2026-10-21.md`. No acceptance status changes.

Pure-Simple file-open ABI probe4 PASS with explicit fixture input: existing UTF8path readonly open/read/close and missing-file rejection. Initial failed run omitted ignored .txt fixture; GDB proved correctraw3arguments, then authoredfixture was copied explicitly and marked intent-to-add incompletion. Updated generator5 PASS fullbyteparity56,367bytes SHA e4303bed71db6a425139128c7d2d158765c9212c075c3cda325c75fa6ed509e3;134HIR/219ASTvariants. Negativepreflight checks PASS for missingASTsources and singlemissingASTPatternKind with bothoutputsentinelsunchanged. Canonicalmemory attempts4(48GiB) and5(40GiB) were refused byfresh75%MemAvailable admission; refusals retained, no enforcement bypass or repeatedlaunchuntilmeaningfulbudgetchange. Identicalv3 modulecontrol4 runs threads1,HIRCACHE0 (adopted0,disabled reasonoff), preservingallpriorcaches, to distinguish typeidentityproducer bugs beforebroadsourcerewrites.

Correction to preceding memory-refusal interpretation: source inspection of bootstrap/lib/tree-rss-policy.shs proves COMPILER_RSS_CEILING_KIB is elevation-only and requires STRICTLY GREATER than existing48GiB ceiling. Attempts4-6 used equal/lower values, so those invocations were invalid even where headroom fit. Canonicalattempt7 unsets elevationoption andusesordinary40GiBPROCESS_TREEcap underunchanged48GiBhardceiling/enforce/jobs1. This corrects invocation guidance, notpolicycode; historicalrefusals retained. Generatornegativecases missingASTandmissingPatternKindbothPASS preservingoutputsentinels.

### 2026-10-21 local pure-Simple repair continuation

- Identical-source manual module control 4 failed 13/419 modules with HIR cache disabled, adopted zero, and one worker (869.79 s; 6,682,104 KiB). This does not support a cached-HIR handoff cause. Failed objects and caches retained.
- Concrete struct absence guards and enum discriminant probes passed. The production symbol-family owner probe rejected a verified foreign enum with tag zero and retained valid SymbolKind tag zero. Astra requested rejecting legacy family ID zero as well; source now requires positive family ID, and a strengthened native probe is pending.
- Targeted optional payload rebindings, qualified enum pattern owners, and direct MirTerminator declaring-module imports are frozen in v7 (177 inputs). Manual module object attempt 5 is running with the admitted pure-Simple r17 producer and existing object cache.
- Canonical Stage2 refresh attempt 7 remains running on separate immutable v5 source with normal enforced 40 GiB process cap and the default 48 GiB hard ceiling. No deployment occurred; compiler/runtime qualification and the 44 acceptance items remain open.

- Manual module attempt 5 completed FAIL: 6/421 modules, down from 13/419; 1,133.03 s, 7,471,464 KiB. Final diagnostics retained in frozen-tree `manual-module-errors-5.json`. Additional qualified enum patterns, typed constructor candidates and contextual diagnostics received Astra approval; attempt 6 runs frozen v8 with 180 reconciled source inputs.
- Focused native Ret-owner probe build/run PASS: concrete MirTerminator parameter accepts Ret(None), rejects Unreachable, while HirExprKind controls remain distinct. This does not qualify SSA or identify the remaining aggregate owner error. No speculative SSA rebind applied.
- Redeploy route audit found existing clean explicit immutable-generation promoter; main-tree version is concurrent dirty work and preserved. Missing scoped toolset-admission producer and launcher resolution remain documented in `build/nogc-hardening/local-redeploy-promotion-handoff.json`; no deployment occurred.

- Manual object attempt 6 completed FAIL: 4/421 modules (1,123.25 s; 7,469,264 KiB), reduced from 6 and earlier 13. Proven residual source bugs found: synthetic-driver HIR traversal used Ret instead of Return; call evidence matched optional EnumLit payload directly. Both fixed and Astra-reviewed. Direct MirBinOp import in expr_dispatch also reviewed; attribution remains pending.
- Canonical attempt7 was stopped with exit143 after confirming its immutable v5 still contained the exact proven Ret/Return error. Only the owned seven-process tree was terminated; caches/logs retained. This is cancelled obsolete source, not a build PASS or OOM result.
- Manual object attempt7 runs frozen v9 (183 source inputs), one-pass HIR with SIMPLE_HIR_CACHE=0 and existing parse/object caches retained. Existing admitted-r17 SIMPLE_ENUM_PAYLOAD_TRACE=1 is enabled for concrete module/line mismatch evidence.
- Added real Return/None and optional-enum-payload regression assertions. One interpreter-runner attempt could not execute either file because minimal r17 rejects public run; both remain NOT_EXECUTED. No green assertion or runtime qualification claimed.

### Local pure-Simple object recovery — final bounded cycle

Manual module attempt9 (frozen v11) completed FAIL: 420/421 modules lowered, one failed module emitted two `undefined variable MirBinOp` errors; 1000.79s and 6,713,996 KiB maximum RSS. Actual enum inspection identified two nonexistent `MirBinOp.Or` variants in byte-array guards; both now use declared `MirBinOp.BitOr`, with scoped Astra approval. Attempt10 is the final bounded cycle, running on frozen v12 (187 source inputs) with preserved cache8. No local deployment or acceptance closure is claimed.

Final attempt10 terminal result: **RESOURCE_ABORTED**, exit143. All421 HIR modules, all421 MIR modules, and all421 native-cache preparation modules passed with zero MIR failures. The two BitOr fixes therefore clear the previous lowering blocker. Native codegen had380 uncached modules and remained at checkpoint41/421 while owned process-tree RSS reached42,817,428 KiB, above the40GiB bound (41,943,040 KiB); exact owned producer processes were terminated and reaped. No entry object, full CLI, admission or redeployment was produced. Final bounded cycle exhausted; no attempt11. Logs/cache/frozenv12 remain preserved. All44 acceptance criteria remain open.
