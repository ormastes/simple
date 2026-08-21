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
- verify: Updated push/bootstrap/tiering self-tests passed; the real ref fixture
  remained within the ten-second budget. Full bootstrap remains blocked by the
  unchanged Stage-3 imported-type cascade after the third bounded cycle.
- fix-pending-verification: The unchanged impossible dependency payloads were
  localized to the two staged `Dict<text, ModuleSurfaceCallable>` value reads.
  Surfaces now retain aligned callable name/value arrays and registration uses
  their scalar index, with a source contract and tracked resume command. No
  fourth bootstrap was launched after the three-cycle cap.
