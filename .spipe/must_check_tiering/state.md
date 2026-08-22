# Feature: Must-Check Tiering

## Raw Request

Harden the repository's mandatory checks by separating a roughly ten-second
commit/push check from expensive bootstrap checks. Persist successful expensive
checks in a textual SDN database so a later lightweight check can prove which
mandatory items have passed, while new or stale items remain actionable TODOs.
An ad-hoc successful bootstrap must refresh the evidence consumed by the next
push check. The broader request also names sdoctest terminology/documentation,
server/GPU performance, SimpleOS/QEMU/SBC/toolchain, RISC-V/VHDL/Linux, and
binary-size/startup/benchmark goals; those remain mandatory tracked outcomes but
must not make the interactive push hook unbounded.

## Task Type

code-quality

## Refined Goal

Create a fail-closed two-tier mandatory-check system whose push tier completes
in about ten seconds and whose bootstrap tier executes and records expensive
requirements in a human-readable SDN ledger that the push tier validates for
freshness and completeness.

## Acceptance Criteria

- AC-1: The canonical commit/push entrypoint runs only bounded static and ledger
  validation checks, has an executable timing test with a 10-second target, and
  does not invoke full tests, native builds, QEMU, physical boards, or live
  performance comparisons.
- AC-2: A canonical bootstrap mandatory-check entrypoint owns all expensive
  gates moved from commit/push and fails closed when any required gate fails,
  is unavailable, or emits no valid verdict.
- AC-3: The bootstrap entrypoint writes a deterministic textual SDN ledger with
  each gate's stable ID, status, source revision/fingerprint, command, completion
  time, and evidence reference; the push entrypoint rejects malformed, missing,
  failed, unknown, or stale push-blocking rows while reporting non-blocking TODO
  rows distinctly.
- AC-4: Any successful canonical or ad-hoc bootstrap run updates the same ledger
  so the immediately following push check accepts its fresh evidence without
  rerunning expensive work.
- AC-5: Mandatory outcomes not yet achieved stay visible as actionable TODO or
  blocked rows with owner/unblock evidence and can become pass only through a
  successful bootstrap-owned gate; they are never silently skipped or counted
  as pass.
- AC-6: Focused automated tests prove the tier membership, timeout/budget,
  malformed/stale ledger rejection, failed push-blocking row rejection, TODO
  preservation and reporting, successful
  bootstrap-to-push transition, deterministic update, and no expensive command
  execution from the push tier.
- AC-7: The broader named outcomes (Markdown/comment sdoctest discovery, server
  GPU/performance parity, SimpleOS SBC/QEMU/toolchains/executables, shared
  RV32/RV64 and Simple-generated VHDL/Linux boot, and binary/startup/benchmark
  parity) are represented by bootstrap-tier gate or TODO IDs rather than being
  dropped from the mandatory contract.
- AC-8: Knowledge is updated in the relevant `doc/` research/architecture/design
  and plan artifacts, the operator-facing `doc/07_guide/` page, both feature and
  layer expert wiki skills under `doc/00_llm_process/`, and `glossary.md` with
  the `sdoctest` terms for Markdown and source-comment tests; every discovered
  unfixed gap has a `doc/08_tracking/bug/` record with file/line and unblock
  condition.
- AC-9: Because this changes workflow/evidence contracts, matching generated or
  manual `doc/06_spec` documentation and applicable `.codex/skills/`,
  `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, and
  `.gemini/commands/` guidance are updated or explicitly marked N/A, and the
  generated manual is understandable without opening the executable spec.
- AC-10: Final focused verification runs every acceptance command at most once,
  records the push-tier wall time, observes the three-cycle cap, and does not
  claim the broader hardware/performance outcomes complete without their actual
  evidence.

## Scope Exclusions

This lane restructures and hardens when the named expensive requirements run;
it does not itself implement the web/database GPU engines, SimpleOS toolchain,
SBC/Linux boot, RISC-V/VHDL generators, or performance parity features.

## Cooperative Review

Parallel read-only review lanes: `bootstrap_phase_audit` owns compiler-phase
receipt mapping, `push_budget_audit` owns fail-closed and timing review, and
`must_check_tests_docs` owns focused test/manual/wiki routing. The current
primary agent is merge owner, final reviewer, and generated-manual reviewer.
Shared names are `push_must_check`,
`bootstrap_must_check`, and `must_check_ledger`; manual steps are
`step("Run the lightweight push must-check")`,
`step("Run the bootstrap must-check")`, and
`step("Validate the must-check ledger")`; setup/checker helpers use the same
names, and any temporary scenario oracle must use `fail(...)`.

## Phase

implementation-blocked-by-bootstrap-authority

## Log

- dev: Created state file with 10 acceptance criteria (type: code-quality).
- dev: Added three parallel read-only review lanes at the user's request.
- research: Confirmed the pre-push fan-out includes minute-scale native/compiler probes and mapped authoritative Stage 1-4 bootstrap evidence.
- design: Selected a registry/producer/ledger/consumer split with unique rows, content fingerprints, and atomic updates.
- implement: Added lightweight push delegation, bootstrap phase verification, SDN registry/ledger, focused tests, and operator/wiki documentation.
- implement: Added bootstrap Caret-suite rows and Kimi agent-runtime wrapping; added a bounded parent-owned multi-Caret manager as an automated gate while retaining honest TODO rows for real `os.apps.smux` integration and Slang-through-Caret inference.
- harden: Bootstrap completion now runs all automated bootstrap-tier gates in the same invocation after individually validating compiler Stages 1–4; self-test-only runners cannot be enabled in production.
- harden: Automated gate logs are retained under the source fingerprint and every PASS requires a timestamp plus an evidence reference; the push consumer rejects evidence-less PASS rows.
- harden: Ledger schema v3 requires a stable owner and actionable unblock
  condition on every unfinished row, rejects PASS rows with pending unblock
  text, and exercises bootstrap-produced state through the real committed-ref
  push consumer. The Unix installer now recognizes exact copied legacy guards
  as well as symlinks without overwriting an existing preserved hook.
- perf-fix: The dispatcher skips an exact canonical guard duplicated in
  `pre-push.local`, preventing the bounded must-check from running twice while
  continuing to chain any non-identical local hook.
- bootstrap-cycle-1: The receipt-free Stage-2 trust-root lane failed in the
  Rust authority build with E0433 because `dispatch_profile.rs` was again
  undeclared. Restored exactly one owner and wired the existing millisecond
  guard into the pushed-ref tier so this defect fails before Cargo/bootstrap.
- artifacts: Added user-selected feature/NFR requirements and the missing
  executable `test/03_system/check/must_check_tiering_spec.spl`. Its manual is
  source-reviewed, but Stage-4 execution/docgen remains pending because this
  isolated worktree contains no admitted `bin/simple`; no seed was substituted.
- audit: Corrected Caret evidence boundaries: `local_torch` does not prove Slang inference, and `AgentTmuxEmbed` does not prove `os.apps.smux`; both claims remain explicit TODOs while the bounded multi-manager has its own automated row.
- verify: Focused tiering/ref-path test passed in 2s (real ref path 0s); Caret and sdoctest parser self-tests, Unix hook check, working/staged direct-env guards, shell syntax, and scoped diff checks passed.
- blocker: A full bootstrap cannot start because no canonical admitted Stage 2 parent and planner-admission-v2 receipt exist in `build/bootstrap`; the deployed `bin/simple` is a Rust seed and was not accepted as verification evidence.
- blocker-detail: The repository's open genesis defect confirms no production path writes `stage2-sanity.receipt` and `stage2-provenance.receipt`; the only admission producer requires those files, so a fresh tree cannot produce the receipt needed to start Stage 1.
- harden: Restored the narrowly scoped `--full-bootstrap --stop-after-stage2`
  measured trust-root lane and bound its parent markers to the immutable Stage-2
  admission receipt. The planner producer now replays the full admission
  verifier instead of accepting marker text or unreferenced digest strings.
- verify: The isolated Slang + must-check branch passed the 41-case Slang setup
  contract and the must-check tiering contract. The planner producer fixture
  was not rerun after its third fix cycle; final verification remains pending.
- blocker: The first isolated measured-genesis run stopped in the Rust authority
  build before Stage 2. Current `origin/main` has duplicate
  `eval_dict_for_each`, a missing `interpreter::dispatch_profile`, and a missing
  `exec_block_closure_into` export. Those fixes are staged in another active
  lane and were not appropriated. See
  `doc/08_tracking/bug/bootstrap_rust_authority_compile_blockers_2026-08-21.md`.
- verify: The real committed-ref push check completed in 0s and failed closed
  because the source-bound compiler Stage 1-4 ledger rows remain TODO. This
  proves the interactive budget and refusal behavior; it is not a release PASS.
- progress: After rebasing onto the upstream duplicate-helper fix, the Rust
  authority still lacked `interpreter::dispatch_profile`. Restoring the module
  made `cargo check -p simple-compiler` pass and allowed bootstrap to enter the
  pure-Simple Stage-2 native build.
- blocker: Stage 2 then rejected `_FlatAstBridge/convert_nodes.spl` because it
  constructed undeclared `PatternKind.TypeTest`. The enum variant is now added
  last to preserve ordinal ABI, and the stage-log diagnoser now recognizes the
  uppercase native-build summary (11 fixtures PASS). A fourth bootstrap run is
  prohibited by the three-cycle cap, so Stage 2-4 evidence remains pending.
- progress: A fresh measured run admitted Stage 2, produced a canonical
  planner-admission-v2 receipt, and replayed Stage 2 successfully under the
  Stage-4 authorization. Explicit sibling-impl imports removed all prior
  Stage-2 link failures.
- blocker: Stage 3 now fails closed in HIR lowering with 410 distinct
  file/type failures across 197 modules for seven imported types. This is a
  broad self-host import/re-export resolution defect, not justification for
  consumer-by-consumer imports or seed fallback. See
  `stage3_selfhost_imported_type_resolution_cascade_2026-08-21.md`.
- fix: Root-cause analysis found Phase 3 dispatch trusted a native-unstable
  readiness boolean after Phase 2 intentionally emptied `ctx.modules`. Routing
  now uses stable streaming configuration, rebuilds only from the frozen
  surface owner, and fails closed before an empty parser-cache read. The focused
  lifecycle regression invokes the production dispatcher. Bootstrap rerun is
  deferred to a fresh session because this session reached its verification
  cycle cap.
- verify: A fresh admitted Stage 2 confirmed production Stage 3 now selects
  streaming HIR. The remaining 197-file imported-type cascade was traced to
  eager package-sibling signatures whose owner-private named/glob import routes
  were read from copied `ModuleSurface` aggregates. Dependency resolution now
  reads the canonical frozen surface, accepts only unambiguous explicit glob
  terminals, and has a focused glob plus named-reexport sibling regression.
- blocker: Two subsequent cache-preserving Stage-3 attempts crashed with
  signal 11 during Phase-2 streaming surface parsing at different files (after
  40 and 5 released surfaces). An isolated 28-module HWIR closure compiled and
  ran successfully, disproving the last progress file as a deterministic source
  failure. The three-cycle cap is exhausted; see
  `stage3_streaming_surface_parse_nondeterministic_segv_2026-08-21.md`.
- fix: Static lifecycle audit excluded cleanup ordering as the direct cause
  because the scope was already paused. It instead found parser scratch arrays
  reusing potentially reclaimed backing via `clear()`, plus file-local generic
  constraint dictionaries retained across scopes without reset or promotion.
  Parser init now replaces/resets those owner-local graphs; cleanup ordering is
  separately canonicalized and both invariants have source contracts.
  Re-verification is deferred because the current session exhausted its
  three-cycle cap.
- verify: A fresh bounded run proved the type-pool whole-owner fix by releasing
  all 954 streaming surfaces and entering HIR. The prior parser SEGV record is
  resolved.
- blocker-correction: Full-log review showed the first HIR failure was
  `FrontendAsmTargetSpec`; later directory and shared-type errors were cascade
  symptoms. The alias workaround is removed. Callable dependency routing now
  gives explicit named imports precedence over overlapping globs while keeping
  same-precedence ambiguity fail-closed, with behavioral and source-contract
  regressions. Fresh bootstrap verification remains pending.
- harden: The SDN registry now owns the four bounded push commands; the push
  consumer rejects manifest/ledger command drift and missing or SHA-mismatched
  PASS evidence. Bootstrap automation accepts only an explicit final PASS
  verdict, and Sdoctest bootstrap evidence requires independently nonzero green
  Markdown and source-comment lanes.
- fix: The fresh Stage-2 build exposed a partially integrated callable-signature
  projection: its consumer referenced `ModuleSurface.signature_names`, but the
  fields, producer, registry helper, and live consumers never landed. Removed
  that dead partial path and added a source contract rejecting undeclared scalar
  signature consumers; the reference-semantic callable lookup remains the
  coherent owner pending an atomic replacement.
- blocker: The third and final cache-preserving Stage-2 cycle cleared the
  undeclared `ModuleSurface.signature_names` HIR failure, then failed at link:
  `module_surface_declarations` calls the missing global owners
  `module_surface_projected_type_shape` and
  `module_surface_projected_type_name`. Strict bootstrap refused seed fallback.
  The session verification cap is exhausted, so no fourth bootstrap or Stage-2
  PASS is claimed. Evidence is in `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.
- verify: After rebasing onto the missing projection-owner fix, a fresh
  source-bound four-core Stage 2 completed, passed sanity/receiver proofs, and
  published an immutable admitted parent. The canonical planner-admission-v2
  producer authorized the one-thread Stage 3 recovery lane.
- blocker: Stage 3 parsed/promoted/released all 687 surfaces in 458,677 ms and
  entered HIR, proving the former surface crash fixed. RSS then rose from
  638,492 KiB during late parsing to 3,599,144 KiB at HIR 1/687 and 7,341 MiB;
  host `earlyoom` sent SIGTERM at 13:08:44 UTC when available memory fell below
  10%. Exit 143 is resource-unavailable, not PASS or a compiler diagnostic.
  The existing Pure-Simple immortal-allocation bug record now carries this
  measured evidence; Stage 3/4, optimizer, SPipe/docgen, deployment, and ledger
  publication remain pending.
- perf-review: The owned compiler edit removes an unreachable projection method
  and unused import, adding no hot-path loop, allocation, copy, data-layout, or
  dispatch work and preserving the existing Pure-Simple callable API. The
  meaningful remaining regression is the measured Stage-3 HIR RSS blocker
  above; no C/Rust substitution is accepted.
- verify-post-rebase: The single final focused batch passed the real interpreter
  owner guard selftest/local/ref paths (13/13 modules each) and the complete
  must-check tiering contract. Push selftest took 4s, committed-ref validation
  1s, and installed-hook validation 0s; the combined batch took 14.13s with
  108,288 KiB peak RSS. Each push path independently satisfies the 10-second
  NFR. The Simple optimizer was not run because Stage 4 remains unavailable;
  the admitted Stage 2 artifact is not general optimizer/SPipe evidence.
- docs-audit: Operator manual, guide, feature expert, bootstrap layer expert,
  glossary, Unix/Windows installers, and `doc/06_spec` layout are present; the
  layout scan found zero executable `*_spec.spl` files under `doc/06_spec`.
  `doc/01_research/domain/must_check_tiering.md` remains missing and must be
  produced through the required domain-research tooling before goal completion.
- verify: Updated push/bootstrap/tiering self-tests passed; the real ref fixture
  remained within the ten-second budget. Full bootstrap remains blocked by the
  unchanged Stage-3 imported-type cascade after the third bounded cycle.
- fix-pending-verification: The unchanged impossible dependency payloads were
  localized to the two staged `Dict<text, ModuleSurfaceCallable>` value reads.
  Surfaces now retain aligned callable name/value arrays and registration uses
  their scalar index, with a source contract and tracked resume command. No
  fourth bootstrap was launched after the three-cycle cap.
- blocker-correction: The aligned aggregate array caused a fresh Phase-2 SEGV
  after 11 released surfaces because it duplicated nested callable ownership.
  That representation is removed. `ModuleSurfaceCallable` is now a single
  promoted class owner in the existing dictionary, so staged lookup transports
  a reference rather than a large value aggregate.
- verify: Cycle 2 parsed and released all 664 Stage-3 surfaces without a SEGV,
  proving the callable class owner fix. HIR then failed closed with 1,352
  diagnostics across seven unresolved imported types.
- fix-pending-verification: The surviving route consumers read nested
  `ParserImport`/`ImportItem` aggregates across the staged boundary. Freeze now
  emits aligned scalar item offsets/counts/source/local names, and both callable
  dependency and re-export traversal consume only that projection. One final
  bounded bootstrap cycle remains.
- verify-fail: Cycle 3 passed fresh Stage-2 admission and replay, then Stage 3
  failed with 1,347 HIR fatals across 200 modules (six unresolved types and
  seven unresolved names). Stage 4 was unavailable and seed fallback was
  refused. No fourth cycle is permitted in this session.
- blocker-correction: Primary import registration and private facade/glob
  expansion in `module_import_resolution.spl` still read nested
  `ParserImport`/`ImportItem` aggregates before the two converted consumers.
  The exact owner, evidence, regression requirements, and next-session unblock
  are recorded in
  `stage3_primary_import_resolution_aggregate_corruption_2026-08-21.md`.
- fix-pending-verification: A fresh bounded session claimed that owner. Frozen
  surfaces now retain authored module spellings, primary registration and
  private facade/glob expansion consume only scalar route arrays, invalid
  projections fail closed, and `ProcessResult`-shaped return-only plus alias
  regressions cover the exact and adjacent roots. Bootstrap cycle count is 0/3.
- verify-fail: Fresh cycle 1 passed Stage-2 admission and replay, then Stage 3
  reproduced the early Span/OptimizationLevel/ProcessResult HIR cascade. No
  crash occurred; Stage 4 was unavailable and seed fallback was refused.
- fix-pending-verification: The remaining free-function, concrete-impl, and
  trait-method consumers read retained callable aggregates across the staged
  boundary. Surfaces now freeze aligned scalar signatures, dependencies, and
  impl-to-trait relations; unsupported complex shapes fail soft. Bootstrap
  cycle count is 1/3.
- verify-fail: Cycle 2 again passed Stage 2, but Stage 3 reproduced the exact
  early unresolved Span/OptimizationLevel/ProcessResult cascade; Stage 4 and
  deployment were correctly refused.
- fix-pending-verification: Declaration discovery itself still used staged
  Dict membership before any scalarized consumer could run. Import routing and
  terminal-kind discovery now select composite/enum/trait/alias/callable/const
  declarations through frozen scalar name arrays. Bootstrap cycle count is 2/3.
- verify-fail-blocked: Final cycle 3 passed Stage 2 and its replay, then the
  Stage-3 self-host compiler was killed by SIGSEGV (signal 11). Stage 4,
  deployment, the lightweight push hook, and GitHub push remain unavailable.
  The three-cycle cap is exhausted; no seed fallback or bypass was used.
- blocker-correction: Kernel symbolization localized the Phase-2 SIGSEGV to
  `flat_ast_to_module` copying an inline conditionally selected 48-byte Type
  while converting typed extern parameters. Flat AST conversion now uses
  stable Type locals for extern and ordinary parameters and a stable Expr
  local for ordinary defaults, with exact and adjacent regressions. A fresh
  bounded verification session is required.
- verify-fail: Fresh cycle 1 proved the Flat AST repair by releasing every
  streaming surface and entering HIR. The run then reproduced the original
  Span/Type import cascade; it was terminated after the gate was definitively
  failed rather than collecting hundreds of duplicate diagnostics.
- fix-pending-verification: Composite registration now consumes a frozen
  scalar kind/field/dependency projection instead of retained Dict payloads.
  Qualified function/type bind and lookup now use aligned scalar first-write
  indexes, avoiding staged class-field Dict membership. Cycle count is 1/3.
- verify-fail: Cycle 2 passed Stage 2 but Stage 3 faulted during surface
  extraction after parsing `backend_port.spl`. The first composite projection
  implementation reopened `composites[composite_name]` to build its scalar
  rows, reproducing the rich Dict payload hazard inside Phase 2.
- fix-pending-verification: Composite scalar rows are now emitted directly
  from each parser class/actor/struct while its owner is live; surface
  construction never reopens a composite Dict value. Cycle count is 2/3.
- verify-fail-blocked: Final cycle 3 passed Stage 2 and replay, then Stage 3
  again received SIGSEGV after five released surfaces at parse-start for
  `std/nogc_sync_mut/io_runtime.spl`. The same source previously passed after
  the stable Flat AST local fix, so source-layout-sensitive aggregate transport
  remains in the self-hosted Phase-2 path. Stage 4, deployment, push hook, and
  GitHub push were refused. The three-cycle cap is exhausted.
- blocker-correction: Kernel fault `0x4bc8e6` symbolized to
  `flat_ast_to_module`; disassembly shows a conditionally selected 48-byte
  Type copy. Parameter Type/default locals were already stable, but ordinary
  and extern return Types still used the same inline conditional shape.
  Both now use stable typed locals, and the source contract forbids all four
  rich conditional transport forms. Fresh verification is pending.
- blocker-correction: Exact instruction mapping supersedes the preliminary
  Type inference above. Address `0x4bc8e6` is the enum path copying the
  function-wide six-word `Span` after a pool safepoint. Enum construction now
  creates empty spans at each use instead of retaining that aggregate across
  the declaration walk. Fresh verification is pending.
- cycle-1-progress: The enum-local Span refresh removed the SIGSEGV. Stage 3
  released all 663 surfaces and failed closed on an explicit unsupported flat
  expression tag 18 in `module_import_registration.spl`. Tag 18 is the general
  `EXPR_BLOCK`; the bridge now converts it through the existing block helper
  instead of reserving that support for if/lambda callers. Cycle count is 1/3.
- cycle-1-review: Parallel review found that general `EXPR_BLOCK` nodes may
  carry both expanded statements and a tail expression. The shared block
  converter now preserves both; the interrupted pre-admission Stage 2 build
  produced no verdict and was discarded before this correction.
- cycle-2-progress: Generic block conversion passed all 664 surfaces and HIR
  began. The next fault (`0x537356`) maps exactly to a field `HirType` copied
  from retained field metadata: its embedded Span was stale after HIR
  safepoints. Field lowering now retains the resolved kind but reconstructs
  the type with the live expression span. Cycle count is 2/3.
- verify-fail-blocked: Final cycle 3 admitted Stage 2 and its planner receipt,
  passed all 664 Flat AST surfaces, and advanced HIR beyond the former field
  crash. It then recorded deterministic unresolved `Span` type failures in
  `driver_pipeline_passes.spl` (15) and `driver_pipeline_aop.spl` (19). The
  already-failed long scan was terminated under the iteration/runaway guard.
  Stage 4, deployment, lightweight pre-push, and GitHub push were refused.
- resumed-cycle-3-fail: Scalar route validation, canonical direct dependency
  imports, and Dict-free origin lookup reduced the first driver HIR failure
  from eight unresolved types to five unresolved `Span` types, but did not
  converge. The final run reached HIR module 6 at +326955 ms with 777240 KiB
  RSS. This is no material improvement over the diagnostic baseline (+240864
  ms at module 5, 776960 KiB RSS). The three-cycle cap is exhausted; Stage 4,
  deployment, lightweight pre-push, and GitHub push remain refused.
- hook-fix: Reproduced the shared-worktree installer defect with two linked
  worktrees: installation from the first made the second fail because the
  common pre-push hook resolved into the first checkout. Both installers now
  use a stable worktree-resolving launcher; legacy dispatchers are replaced
  rather than preserved recursively. The focused contract passed with
  `selftest=4s ref-path=0s installed-hook=1s` after rebase. The real shared
  hook was then installed and both installer freshness and production wiring
  checks passed.
- doc-refactor: Updated the operator manual, tooling guide, feature expert,
  bootstrap layer expert, SPipe/Codex workflow skills, and the bug record.
  `.agents/skills`, `.claude/agents/spipe`, `.claude/commands`, and
  `.gemini/commands` are N/A for this narrow installation mechanism because
  none names or implements must-check hook installation.
- research: Added the previously missing domain research with primary Git,
  in-toto, SLSA, TUF, NIST, Bazel, GitHub, GitLab, and pre-commit references.
  The selected requirements remain unchanged; no option-selection cycle was
  reopened.
- cross-host-audit: Added `windows-hook-installation` as an explicit
  bootstrap-tier TODO with tooling-team ownership and the native Windows
  two-worktree install/check resume command. PowerShell source parity is not
  counted as native Windows PASS. The updated focused contract passed with
  `selftest=5s ref-path=0s installed-hook=0s` and reported the TODO visibly.
- bootstrap-identity-fix: Reproduced that completion validated an exact Stage 4
  candidate but launched automated gates without binding `SIMPLE_BINARY` or
  the established `SIMPLE_BIN` compatibility name, so a
  stale deployment could supply false evidence. The recorder now canonicalizes
  the candidate only after all four phase proofs pass and overrides ambient
  both identities for every automated row. The focused self-test passed its
  third and final cycle with intentionally conflicting ambient paths; the bug
  record is resolved. The existing interpreter/JIT/native engine differential
  is now bootstrap-automated instead of an inert TODO.
- latest-bootstrap-evidence: A source-matched four-core Stage 2 producer passed
  in 1:11:20 with 2,794,780 KiB peak RSS and no swap. Canonical Stage 3 released
  all 687 surfaces but grew from 11.4 GiB to a measured 26,419,744 KiB peak at
  HIR import processing; the owned child was safely terminated with exit 143.
  Stage 3/4, optimizer, SPipe/docgen execution, and ledger PASS publication
  remain blocked on the tracked recursive HIR/SymbolTable promotion leak.
- automated-gate-contract-fix: The predicate-parser native checker previously
  ignored the admitted Stage 4 identity and preferred an ambient legacy Stage 2
  path; its constant-space resolver now prioritizes explicit diagnostics,
  `SIMPLE_BINARY`, `SIMPLE_BIN`, legacy Stage 2, then the deployed default, with
  all branches self-tested. The essential-tools producer now ends with the
  explicit PASS verdict required by the fail-closed ledger consumer.
- push-performance-review: The canonical push chain remains behaviorally
  bounded only for small outgoing ranges. The completed first slice adds a
  push-only tip mode: it retains all final-tree structural checks, skips the
  exhaustive fixture campaign, avoids revision-list materialization, and uses
  a count-only parent reference. The same 12-commit range measured 25.79s
  before and 1.29s after at 79,872 KiB peak RSS. Multi-ref deduplication and
  evidence-file bounds remain tracked follow-up work.
- push-bound-follow-up: Identical ref updates are now deduplicated, invocations
  above two unique updates fail closed with split-push guidance, and committed
  PASS evidence must remain under the canonical repository root within a
  64 MiB aggregate hashing budget. The exhaustive 24-fixture tree campaign is
  now a bootstrap automated row; interactive push retains bounded tip structure
  checks. The complete focused contract passed in 7.14s at 71,168 KiB peak RSS;
  committed-ref and installed-hook paths reported 1s and 0s respectively.
- committed-rules-fix: The quick rules gate now extracts `rules.sdl` from the
  exact pushed ref and fingerprints it in both producer and consumer. A dirty
  hostile `sleep 30` registry was ignored in favor of the committed passing
  policy. The updated focused contract passed in 7.61s at 71,936 KiB peak RSS;
  ref and installed-hook paths reported 0s and 1s.
