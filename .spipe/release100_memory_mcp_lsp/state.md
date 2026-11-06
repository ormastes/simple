# Release 1.0.0 memory hardening and MCP/LSP improvement

## Raw Request
$sp_dev do memory hardening and mcp lsp improve and land check already impled or not. go pherallel and land on release/1.0.0

## Task Type
feature

## Refined Goal
Audit and implement both user-selected Downloads plans against release/1.0.0, verify every requirement with authoritative evidence, and merge reviewed changes into release/1.0.0.

## Acceptance Criteria
- AC-1: Preserve both input plans byte-for-byte with hashes and map every requirement, acceptance row, formal obligation, and release gate to implementation and execution evidence; missing or indirect evidence remains open.
- AC-2: Complete the memory plan's ownership, short-borrow, cleanup, arena, cycle, pipeline, cache, hashing, process, budget, metrics, migration, and independent-gate requirements across its specified backend/host matrix.
- AC-3: Complete the MCP/LSP plan's provider, snapshot, session, source-view, help, annotation, diagnostic, debug, environment, change-analysis, protocol, edit-transaction, performance, and security requirements and acceptance gates.
- AC-4: Run applicable pure-Simple checks, real SPipe assertions and generated-manual review, runtime/MCP native smokes, performance evidence, direct-env guards, and full release-bound test gates once per unchanged criterion. No seed substitution or false PASS.
- AC-5: Update affected research, architecture, design, plans, doc/07_guide, doc/06_spec, feature/layer expert wiki, and bug records. Review skills/agent/command guidance for changed tooling contracts; record N/A only with specific reasons. Retain named owners and actionable unblock conditions for all outstanding evidence.
- AC-6: Review exact PR heads and comments, resolve regressions, and merge only this lane's verified work into release/1.0.0; preserve unrelated dirty work. No tags or publication are requested.

## Scope Exclusions
None from either selected plan. Incremental commits do not imply full goal completion.

## Cooperative Review
Parallel normal-capability lanes: memory_audit, mcp_lsp_audit, release_gates. Root owns integration and final review. Source ownership and shared interfaces will be fixed before parallel implementation. Existing canonical interfaces and manual helpers take precedence; new unresolved test oracles must fail explicitly. Root owns generated-manual review. Lower-model sidecars N/A: current agents perform evidence-sensitive audits directly.

## Phase
implementation-in-progress

## Log
- 2026-11-06: User selected both existing plans and parallel implementation; no new option selection inferred. Fetched origin/release/1.0.0 at e2ce7042552 and created isolated worktree. Original checkout remains untouched.

## Input integrity
- `simple_nogc_ownership_memory_hardening_plan.md`: SHA-256 `016c3718dfe49a9589f008609baee2196a4bce49d26238a7b95974cf2962c4d7`
- `simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md`: SHA-256 `72db8b8cc045ab51f31748684182583f370f08632e612764643cef69710b6021`

## Current evidence and ownership
- Baseline audits: `doc/08_tracking/audit/release100_memory_mcp_lsp_2026-11-06/` (source inspection, not execution PASS).
- memory_audit owns strict no-GC bypass policy propagation in compiler driver and focused tests/docs.
- mcp_lsp_audit owns empty-file/warning/path diagnostic truth and focused tests/docs.
- source_view owns new shared contracts/session/projection and source-open protocol wiring, with explicit unsupported capability boundaries.
- debug_truth owns shared-debug routing/fabrication removal after file-scope review.
- traceability owns the release100_memory_mcp_lsp requirement/design/plan documents.
- Root owns integration, final review and PR landing. Existing root checkout dirty work is outside scope.
- Release verification is pending an admitted full pure-Simple CLI. Stage2 admission permits only scoped compiler probes. Its full-CLI child failed on old source; the outer verifier continued standalone runner work. Neither establishes Stage4 qualification.

## 2026-11-06 implementation checkpoint
- Planning/input/audit PR #7233 merged at `92d4e0ed83f65157a6441f929aa29f66d090e7ed`; recovery clarification PR #7234 merged at `59c4af17045175701f6db8931a7c7a53274d556f` on release/1.0.0. These documentation merges close no product acceptance row.
- Implementation branch: `work/release100-hardening-implementation-20261106`. Strict no-GC bypass policy, diagnostics truth, debug unsupported receipts, and bounded L0 raw source route are authored with focused regressions/manuals/guides/wiki.
- Static peer review found no P0/P1 in these incremental changes. It found and resolved explicit byte-budget units, partial-diagnostic producer-status preservation, and the admission-to-eviction test seam. This is not execution evidence.
- Runtime tests and generated-manual qualification are NOT_RUN. One diagnostic attempt with the unadmitted deployed binary failed before running tests in existing bounded_bytes syntax; it is not PASS and will not be used as fallback.
- Freeze this source for an isolated canonical pure-parent bootstrap prerequisite. No source edits during the active frozen build. Retain failed receipts and caches; the goal stays active and the full selected plans remain open.

## Next implementation lane — 2026-11-06

The first source slice is frozen at `77b05b3a4fb6a3cb3c5b92c2b74cea56b4799b74` in `/private/tmp/simple-release100-hardening-20261106`, with draft PR #7237. Its canonical pure-parent refresh is owned by release_gates; build records live under `/private/tmp/release100-hardening-bootstrap`. That source must not change while building.

Further selected requirements proceed separately in `/private/tmp/simple-release100-next-20261106`, branch `work/release100-source-memory-next-20261106`, based on the same commit:

- source_view: native Simple outline provider, exact structural ranges/focused selection and source_open wiring; canonical inline-body outline parser repair. SDN/SHS spans/dialect and authenticated first-help remain explicit dependencies.
- memory_audit: shared typed-HIR ownership facts/CFG adapter over existing OwnershipFlow; whole-closure preflight and direct interpreter ingress. Audit actual CLI/core interpreter routing before claiming route coverage; SMF artifact admission remains distinct.
- mcp_lsp_audit: authenticated logical-session host using genuine manager authority; no transport/prose/session-metadata inference. Establish actual credential publisher/verifier and consuming ingress before claiming live isolation.
- debug_truth: canonical LspServer full-sync/version ownership and revision-bound code-action conversion; reject malformed/overlapping edits and disk/overlay mismatch. Unsaved-source analysis requires an actual compiler snapshot interface.
- Root: interface and ownership coordination, review, traceability, and eventual release-targeted landing. No product acceptance row closed by static work alone.

All full-plan acceptance requirements remain in scope. Each new regression must exercise real behavior and retain execution status; unadmitted tools and authored manuals cannot supply PASS.

## Next-lane review and formal evidence checkpoint

- Independent memory review identified and is tracking: missing imported checked effects, ownership-sensitive global/capture provenance, derived short-borrow place sets, legal projected refill, and work charging. Canonical Write(place) now distinguishes assignment validation from ordinary Read before Revive; integration review and execution remain pending.
- Native Lean 4.30.0 proved 28 exact Place/Read/Move/Write/Revive/merge lemmas and the independent kernel axiom audit admitted only the documented standard foundations. See `doc/03_plan/release/1.0.0/ownership_flow_formal_refinement_2026-11-06.md`. The eight production-solver twin scenarios are NOT_RUN; all umbrella FV obligations, HIR extraction and compiled refinement remain OPEN.
- LSP review drove exact byte quotas, snapshot-map reuse, malformed/ambiguous action rejection, bounded disk reads and loss-of-sync invalidation. Runtime and live multifile/unsaved-overlay/diagnostic provenance evidence remain open.
- Source-session review requires fresh authorization time after locking, bounded revoked/dead-row reclamation, explicit immutable workspace roots, same-process opt-in manager hosting, and canonical opaque owned-process leases. Raw PID existence is not credential authority. The owned_agent_lease lane owns the canonical manager lifecycle extension; source_auth_review owns independent review.
- Structural provider work repairs canonical inline-body and use/group/relative-import parser defects, rather than introducing a competing viewer parser. Structural/runtime acceptance remains pending.
- Bootstrap owner observed the frozen first slice finish HIR1607 and enter MIR (task4/6), with warnings retained and no terminal verdict. Only its actual admitted receipts can unlock runtime qualification.

## Local reviewed-slice checkpoints

- `39563cbed06`: native structural source views, canonical outline parser fixes, shared source service and focused specifications. Final source review resolved ancestor pagination and query/result identity. The canonical lexer already converts token spans to UTF-8 byte offsets; no second conversion was added. Execution remains NOT_RUN.
- `6a4a4bee184`: bounded LSP document authority and revision-bound code-action conversion. Independent final reread resolved equal-version conflicting-change trust and CRLF boundaries; no unresolved static findings in that slice. Runtime, live multifile/unsaved-source analysis, and diagnostic provenance remain open.
- Auth/owned-process review cycle2 requires consumed-error collection cleanup to release the consumed lease while preserving the failure and retryable pin cleanup. Tests remain NOT_RUN.
- Memory review cycle3 is pending the final direct-contract, resolver provenance, physical-alias, and canonical bounded-encoder integration. The encoder writer's output limit alone did not bound recursive traversal; the codec generator/owner is being repaired rather than treating that limit as evidence.
- These local commits are checkpoints, not release admission. PR #7237 remains the unmerged first-slice draft. Do not merge any source slice until its applicable executable and integration gates pass.

## Saved next state and Downloads inventory — 2026-11-06

- User requested saving next work and continuing release/1.0.0; all three Markdown downloads modified today are preserved byte-identically in inputs_2026-11-06. The newly discovered Caret orchestrator plan is under implementation-gap audit; no new requirement option is silently selected.
- Input `simple_nogc_ownership_memory_hardening_plan.md`: 108049 bytes; SHA-256 `016c3718dfe49a9589f008609baee2196a4bce49d26238a7b95974cf2962c4d7`.
- Input `simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md`: 124178 bytes; SHA-256 `72db8b8cc045ab51f31748684182583f370f08632e612764643cef69710b6021`.
- Input `simple_caret_orchestrator_shared_daemon_full_plan_2026-11-06.md`: 113358 bytes; SHA-256 `07bcd1b91ddb0d053a4ca426ad8fece750a59361d14e96fdcd19a7bc06cbc593`.
- Source-session and owned-process final targeted static review cycle3 found no remaining identified P1/P2. Native process, concurrency and HTTP tests remain NOT_RUN.
- Memory targeted review count is 4 of the user-authorized maximum6 (user AGENTS cap takes precedence over skill3). Cycle4 moves bounded typed-HIR validation before recursive classification/inference and adds deep-type regressions; independent review pending. Counts are not reset.
- Bootstrap first-batch completion was not whole-program completion. Owner is installing identity-bound supervision with a deadline of original attempt start+7200 seconds, preserving caches and canonical termination receipts. No compatible old cache authority was established; no runtime admission yet.
- Cycle4 independent targeted memory review completed: prior ordering P1 addressed, no new findings in scope; all executable regressions remain NOT_RUN. Working direct-env guard and tracked whitespace check passed for the saved next checkpoint.

## Release reconciliation — 2026-11-06

- Rebased six owned commits in `/private/tmp/simple-release100-reconciled-20261106` onto release `6beb0b4463db0fb309db7a74bf1c9120ad15ebce`. Only codec owner files overlapped; generated conflict resolved preserving upstream presence/scalar validation and all113 decoder/placeholder blocks plus97 bounded encoder wrappers. Independent integration review found no new issues. Memory repair count remains4; runtime/regeneration NOT_RUN.
- Frozen bootstrap source and original next checkpoint remain unchanged. Bootstrap session6563 confirmed live with active worker CPU; same fixed deadline retained.

## Canonical overlay analysis continuation

- Current source check API is path-only; no full immutable overlay entry/import analysis API was found. Legacy query parsing and scalar prerequisite probes do not supply semantic snapshot authority. Diagnostic output currently lacks a complete analyzed-snapshot/failure envelope; disk equality preflight cannot exclude ABA.
- Implementation assigned to compiler source-loading owner (debug_truth) and LSP/worker owner (lsp_revision_review), with one shared source_analysis_v1 contract agreed before dependent edits. Design: `doc/05_design/tooling/lsp_snapshot_analysis_2026-11-06.md`. All execution/performance gates remain open.
- Bootstrap session6563 revalidated live, with later module codegen progress. Same original deadline retained; no restart.

## Active implementation and new blockers

- Overlay compiler API, canonical source-provider admission, full DiagnosticV1 retention, original parser diagnostic snapshot codec, LSP owner generations/whole-set requests, idle framing, worker coordination and publication are authored/in progress in the reconciled tree. Do not stage active-owner files blindly. Runtime and generator qualification remain NOT_RUN.
- Provider initial review found unbounded numbered-directory enumeration and missed fully unsaved numbered imports; debug_truth owns repair. Parser typed records require canonical flat-pool codec version update and bounded serialization; source_view owns this with diagnostic bridges owned by mcp_lsp_audit.
- Worker response IPC is moving to a private local owner directory because compiler progress contaminates stdout. This is trusted-local process IPC, not a hostile same-UID sandbox; stronger anchored directory operations remain unavailable on Darwin. Output is never reconstructed from compiler log text.
- Event descriptor ABI has a bounded read-only observation route and scalar signature corrections. Review found the legacy network driver cannot safely distinguish readiness direction or EAGAIN with current native receipts. Cycle3 contains that path with explicit unsupported before any blocking operation, preserving pending cancellation. This DISABLES network completion and is a release blocker for full driver compatibility, not a finished networking repair. Full direction/error/nonblocking capability and real positive native regressions remain OPEN. Memory ownership repair count remains4; event integration count3.
- Frozen bootstrap reported unsupported LLVM i64-to-void conversion in the RISC-V driver text-valued conditional; it remains live collecting work. No speculative source fix was made. Single tiny diagnostic probe is held by build owner pending safe resources and canonical archived-parent admission. Archived binary/receipt hashes match, but replay failed safe-regular-log validation; matching bytes alone are not admission. Evidence lives under /private/tmp/release100-hardening-bootstrap. Same original deadline remains 2026-11-06T08:57:30.426825Z.
- Reconciled PR head a63f2a5eaf7 had plan/structural/rtl-source-truth checks pass, but compiler matrix was skipped; these are not runtime acceptance. Documentation checkpoint d561eb371ae is local while current implementation is integrated.

## Landed verified guard fixes — 2026-11-06

- User requested landing fixes on GitHub. Independently isolated guard repair landed through PR #7278 into release/1.0.0 at merge `487a19d36b1617cc6180b81bb3f46847ac9d938f`; reviewed head `73db6fdc93b2dbf3e1b69fd1fe75f3f4eabfaa3b`.
- Fixed ParserState-qualified field coverage and portable adversarial selftest insertion. Canonical guard on release source passed158 pools and nine fixture groups using default macOS tools; independent exact-head review, working/staged env guards, zero doc executable specs, whitespace, ten blocking push guards passed. No PR findings; no failing check at merge. Broader runtime acceptance is NOT implied.
- Reconciled working guard now matches landed source including portable awk. Original input/source checkpoints and frozen bootstrap remain intact. Full memory/MCP/LSP goal stays OPEN; PR #7265 is still draft and does not have required runtime qualification.

## Bootstrap terminal and integration evidence

- Attempt1 is terminal: canonical watchdog TERM at2026-11-06T08:57:30.571079Z, reaped08:57:32.610869Z. Outer exec6563 exit1; deadline supervisor exit124; RSS receipt interrupted/143, peak7611040KiB. All owned owner/watchdog/coordinator/worker/supervisor processes confirmed absent. Verdict ABORTED atStage2; no CLI or admission. Logs/caches and terminal-result.md remain in /private/tmp/release100-hardening-bootstrap. No automatic restart.
- Provider cycle2 static review closed enumeration/virtual-directory findings. Root confirmed canonical source_root_numbered_candidate_v1 already restricts prefixes to1–3 digits, so finite snapshot probing preserves that grammar; duplicate probe charging and real-world budget/performance still need runtime qualification.
- Private worker artifact cycle2 static review closed initial pin/digest cleanup P2 under the stated trusted-local profile; full16MiB escaped-source boundary control authored. Initial marker-write failure remains explicitly retained/fatal. Native tests NOT_RUN.
- LSP cycle2 is repairing stale disk/environment cache authority with bounded asynchronous validation. Canonical fresh environment fingerprints are being added without resetting other memo owners. Watch/event-index performance, cross-platform async support, full network completion and hostile-filesystem artifact authority remain OPEN. Do not infer full completion from static reviews.

## Overlay implementation checkpoint — not release admission

- LSP freshness targeted cycle2 static review found no new confirmed P0/P1 under the explicitly temporary sequential observed-content contract. Actual scheduler transition specs for handshake hints, edits/close, deferred replies/expiry and shutdown are now authored; all NOT_RUN.
- Fresh canonical identity observer retains unresolved P1: inherited recursive directory listing can allocate/traverse without adequate entry/depth/symlink limits before snapshot admission. Root confirmed eager rt_readdir implementation; a safe facade cannot fix its allocation merely by checking afterward. Source_analysis_environment_fresh_v1_spec.spl exists with two mutation obligations, NOT_RUN. This checkpoint intentionally preserves the issue as OPEN.
- Working direct-env guard, doc executable-spec layout (zero), and tracked whitespace checks passed for the checkpoint. Runtime/manual generation, native lifecycle, cross-platform behavior and performance acceptance remain outstanding. Do not merge this checkpoint on structural green checks alone.
- Canonical candidate-only requalification repair is isolated on branch work/release100-parent-requalification-20261106 in /private/tmp/simple-release100-parser-guard-20261106; release_gates owns it. No candidate execution or source/build restart is authorized until its strict provenance split and negative controls are reviewed.

## Bounded filesystem and producer binding checkpoint

- Bounded native directory owner has real Darwin native behavior evidence, exact seven-ABI/two-provider14PASS, pointer/host mapping evidence, plus selected readdir-error and concurrent accessor/free/reuse controls PASS. This is not Simple/native-LSP or other-platform acceptance. Native owner reached its conservative six-cycle cap and is STOPPED; no additional native feature checks/repairs are authorized without a user exception. Its chronology includes two harness compile failures before the new controls passed.
- Independent provider cycle4 static review found the earlier unbounded fresh walk addressed in source: budgets precede reads/hashes, symlinks rejected, missing versus I/O distinct, handles released. Six Simple regressions NOT_RUN. Existing memoized APIs remain compatible.
- Producer identity now uses the exact parent launch pin and private IPCv2 witness for both modes. LSP cycle3 static review found no new confirmed P0/P1. Direct compiler observations require explicit digest/context and parent validation, not ambient SIMPLE_BINARY or child self-attestation.
- Requalification recovery feature also reached six cycles and STOPPED with a reviewed P1: final admission visibility precedes publication cleanup, and every direct authority consumer needs a commit guard. Historical95/composition31 controls passed but do not qualify any compiler. No candidate was executed. A user question is pending for ONE additional bounded requalification repair cycle; do not proceed without an actual affirmative answer. Evidence: /private/tmp/release100-hardening-bootstrap/requalification-owner-stop.md.
