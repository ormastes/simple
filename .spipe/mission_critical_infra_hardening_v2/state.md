# Feature: Mission-Critical Simple Infrastructure Hardening V2

## Raw Request
`$sp_dev harden simple infra. Simple, simple os, simple rendering, to mission critical, may use some losen version like memory allocatiion. go with pherallel agents.`

## Task Type
code-quality

## Refined Goal
Harden the production Simple compiler/tooling, SimpleOS, and Simple rendering stack to a fail-closed mission-critical release contract, permitting narrowly scoped relaxed memory-allocation behavior only where its safety envelope, resource bounds, recovery behavior, and verification evidence are explicit.

## Acceptance Criteria
- **AC-1 — Authoritative baseline:** Run `scripts/check/check-simpleos-hardening-evidence-matrix.shs` once before implementation and record every current pass, failure, blocked row, stale report, artifact, and exact resume command in the lane plan; the baseline must distinguish compiler/tooling, SimpleOS, rendering, formal proof, CPU/SIMD, LLVM, GPU/QEMU, storage, and memory-allocation ownership.
- **AC-2 — Mission-critical aggregate:** The final canonical aggregate reports `simpleos_hardening_mission_critical_release_status=pass`, `simpleos_hardening_mission_critical_release_blockers=none`, `simpleos_hardening_mission_critical_prereqs_status=ready`, `simpleos_hardening_matrix_passed=26/26`, and `simpleos_hardening_stale_reports=none`; no warning, cached artifact, unavailable host, screenshot, synthetic handle, CPU mirror, or source-only inspection is promoted to PASS.
- **AC-3 — Compiler and tooling:** The production pure-Simple self-hosted binary passes the applicable compiler, library, MCP/LSP, bootstrap-essential-tool, lint, duplication, whole-test, startup/latency/RSS, and direct-env/runtime-facade gates. Any compiler/runtime defect is fixed at the pure-Simple owner boundary first; runtime changes require a minimal reproducer proving the defect is below that boundary.
- **AC-4 — SimpleOS:** SimpleOS evidence proves boot, mount, target-side listing, arbitrary filesystem-program execution, and the compiler/interpreter/loader payload executing from the guest filesystem. Multi-host QEMU work uses the shared big-storage resolver (including `SIMPLE_BIG_STORAGE_CONFIG`), passes `check-simple-qemu-settings.shs`, selects one six-way `--guest` in development and mutually exclusive `--all-guests` for release, and validates exactly 24 unique matrix cells. Every nonpass row retains reason, artifact, resume command, owner, and final reviewer.
- **AC-5 — Rendering:** GUI, Web, Draw IR, Engine2D, Vulkan, RenderDoc, and relevant mobile/host rendering rows prove canonical producer-to-`DrawIrComposition` lowering, real backend provenance, structured interaction evidence, nonblank viewport-matched artifacts, required RDOC magic, and zero-mismatch pairwise ARGB comparison where parity is claimed. Engine3D remains a separate lane and transient font atlas/cache state does not enter Draw IR.
- **AC-6 — Formal and hardware evidence:** The aggregate reports pass for RISC-V RTL/SBY, LLVM port, CPU SIMD, Lean proofs, RISC-V dual-track proofs, critical concurrency, memory safety, storage integrity, GUI RenderDoc Vulkan, and QEMU virtio-GPU access. Host-dependent rows remain active and blocked rather than skipped until genuine device-origin evidence is collected.
- **AC-7 — Relaxed allocation policy:** Define a named, versioned relaxed-allocation profile distinct from the strict default. It must specify where relaxation is legal, fixed budgets/quotas, ownership and lifetime rules, fragmentation and exhaustion behavior, deterministic failure/recovery, observability, and forbidden safety-critical contexts. Tests prove strict mode rejects every relaxed-only path, relaxed mode stays within bounds under stress/fault injection, allocation failure cannot corrupt state or bypass isolation, and the production default remains fail-closed.
- **AC-8 — Concurrency and process safety:** Parallel execution proves bounded-worker runtime-pool use rather than inline fallback, deterministic cancellation/timeout behavior, bounded subprocess capture, and rejection of `pid <= 0` on every kill/wait path. Race, deadlock, exhaustion, and recovery scenarios have executable regressions and formal evidence where required by the aggregate.
- **AC-9 — Requirements and traceability:** Research produces feature and NFR options with pros, cons, and effort estimates; the user selects them before final requirement documents are written. Every selected `REQ-NNN` maps to implementation and a non-placeholder SSpec assertion, and generated/manual specs are readable as operator manuals.
- **AC-10 — Knowledge update:** Refresh affected research, requirements, architecture, design, test plans, agent plans, `doc/06_spec`, `doc/07_guide`, and reports; create/update both `doc/00_llm_process/feature_expert/mission_critical_infra_hardening/skill.md` and the affected compiler/SimpleOS/rendering/memory layer-expert `skill.md` files. Record every unfixed gap in `doc/08_tracking/bug/` with file:line evidence and an unblock condition. Update affected `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, `.claude/commands/`, and `.gemini/commands/` when workflow or evidence contracts change.
- **AC-11 — Verification discipline:** Each criterion receives one authoritative passing result, with no unchanged green reruns and no more than three distinct verify/fix cycles per lane. `doc/06_spec` contains zero executable `*_spec.spl` files, direct-env runtime guards pass for working and staged changes, and final `$verify` reports `STATUS: PASS` before any release handoff.
- **AC-12 — Release integrity:** Release consumes, but does not repair, verification evidence; all external-host rows are genuinely passed, all selected requirements are complete, documentation is current, and no unrelated concurrent-session changes are included in the hardening commit or release.

## Scope Exclusions
- Rewriting Simple features in C or Rust merely to obtain benchmark parity.
- Treating relaxed allocation as permission for unbounded allocation, silent fallback, safety-check removal, or use in formally prohibited critical contexts.
- Claiming physical-board, native-GPU, Vulkan, RenderDoc, or cross-host success from emulation, cached reports, synthetic fixtures, or host-only evidence.
- Releasing before the user has selected feature and NFR options and `$verify` has produced `STATUS: PASS`.

## Cooperative Review
- **Parallel sidecars after this dev phase:** compiler/tooling baseline; SimpleOS/QEMU/storage; rendering/GPU/RenderDoc; memory allocation/concurrency/formal-safety. Each sidecar owns disjoint files and returns findings/evidence to the merge owner rather than declaring completion.
- **Merge owner:** root Codex session.
- **Final reviewer:** normal/highest-capability Codex reviewer after sidecar findings are merged; generated-manual review is owned by that reviewer.
- **Shared interface names:** `MissionCriticalProfile`, `RelaxedAllocationProfileV1`, `HardeningEvidenceRow`, `HardeningEvidenceMatrix` (provisional until research and user requirement selection).
- **Manual flow helpers:** `step("capture mission-critical baseline")`, `step("verify strict allocation policy")`, `step("verify bounded relaxed allocation")`, `step("verify SimpleOS evidence matrix")`, `step("verify rendering provenance and parity")`, `step("aggregate mission-critical release evidence")`.
- **Setup/checker helpers:** `setup_mission_critical_fixture`, `check_relaxed_allocation_bounds`, `check_simpleos_matrix_contract`, `check_rendering_artifact_provenance`, `check_mission_critical_release_status`.
- **Fail-fast placeholders:** all new scaffolds use `assert(false)` or `fail(...)` until backed by real behavior; placeholder passes and skipped unavailable rows are forbidden.

## Phase
impl-in-progress

## Current handoff (2026-08-14)

- Frozen source candidate: `f9d35a3f14e085377a398d8398ec392787c86011`;
  parser/lookup repair `f8f10b7af40`, alias/HIR origin `cc30abb73dd`.
- Stage 2 multiline continuation compatibility was repaired with explicit
  grouping and tracked in
  `doc/08_tracking/bug/stage2_multiline_if_continuation_2026-08-14.md`.
- Bootstrap cycles 1-2 found the same parser divergence at two predicates.
  Historical Restart12 cycle 3 passed both predicates, completed Stage 2 and
  sanity, then observed an unretained Stage 3 exit 139. Later pre-f8 runs
  terminated after high RSS without a candidate. Current source restores the
  typed parser/HIR contract owners and scalar-prefilter lookup; post-f8
  Stage 2/3/4 verification remains pending. The current source also replaces
  the GDB-localized recursive 97-arm `char_to_ascii` FlatAstBridge allocation
  with an unverified range check. The exact typed-receipt bootstrap
  command is in the canonical sys-test plan. Current blocker records are
  `doc/08_tracking/bug/stage2_proof_uses_optional_narrowing_2026-08-14.md` and
  `doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md`.
- Parallel SPipe audits completed: `/root/acceptance_audit` checked
  requirement/evidence traceability and `/root/guide_audit` checked guide,
  manual, state, and process-doc freshness. Root Codex merged their findings.
- Higher-capability internal review `/root/higher_model_review`
  (`gpt-5.6-sol`, xhigh) required three correction rounds and ended PASS for
  truthful resumable plan-document completeness. It explicitly did not pass
  feature verification, release readiness, or external independent review.
- Final traceability verification initially found a manual/source metadata
  mismatch for `MCI-DOC-001/002`; after exact owner/reason/resume alignment,
  `sh test/01_unit/scripts/mci_v2_traceability_contract_test.shs` PASSed. The
  higher-capability reviewer rechecked the final mirror and preserved PASS.
- Frozen scenario vocabulary is the eight `step("...")` strings and helper list
  in the canonical sys-test plan; the provisional helper list above is
  historical only.
- Doc/wiki refactor inventory: updated the canonical sys-test plan, agent plan,
  operator guide, SPipe state, generated/manual blocker text, Stage 3 bug
  record, feature expert, and compiler-driver/memory/UI-render layer experts.
  No workflow/tool API changed, so process skill/agent/command trees are N/A.
- Current classification remains implementation WARN, not verify PASS. External
  producer rows, docgen provenance, independently signed review, and
  `release_blockers=none` remain active.

## Log
- impl continuation 2026-08-13: Canonical Viz composition now rejects any direct-frame quad with a negative or out-of-range `SharedQuadState` index before copying/rebasing it. Negative and equal-to-length malformed-frame regressions are present; self-hosted Simple execution remains pending authority admission.
- impl continuation 2026-08-13: Process V2 cancellation no longer abandons a live child when bounded capture reports a provider error. It retains the first capture/runtime error for the result while continuing TERM/grace/KILL/reap to terminal state; deterministic EIO+TERM-resistant-child regression proves terminal, reaped, and collectable error leases. Canonical strict core-only selfcheck passes.
- impl continuation 2026-08-13: SimpleOS formatted-input APIs (`scanf`, `fscanf`, `sscanf`, `vsscanf`) are now complete as an honest unavailable surface: every declared entrypoint returns `EOF` plus `ENOSYS` instead of a fabricated zero-assignment result or a link hole. Focused strict C coverage passes.
- impl continuation 2026-08-13: Hardened SimpleOS dlmalloc now keeps scanning/validating free-list nodes after selecting an exact-fit candidate; it no longer rejects valid exact-fit allocations merely because another node remains. Focused strict C safety harness passes, including the new two-node exact-fit regression. Guest `limits.h` now guards `SIZE_MAX` against its `stdint.h` provider to permit strict hosted guest-libc harness compilation. The realpath honest-failure C harness also passes under strict warnings after using guest-private errno and a fake kernel syscall dependency.
- impl continuation 2026-08-13: SimpleOS UID/GID facades no longer fabricate root identity: they return unsigned `-1` plus `ENOSYS` until a kernel credential owner exists; focused C coverage passes. The canonical Viz frame builder now rejects non-finite or out-of-range normalized RGBA channels for solid/debug quads; source/integration coverage added, self-hosted execution remains blocked on compiler admission. `madvise` now fails closed with `ENOSYS` rather than silently discarding VM advice.
- impl continuation 2026-08-13: SimpleOS libc scheduler yield now delegates to the kernel-owned syscall 1 rather than returning a fabricated local success; focused ABI/error C harness passes. `realpath` now fails closed with `ENOSYS` instead of returning a copied pseudo-canonical spelling; focused C coverage passes. Canonical Viz surface composition now carries bounded depth/unique-surface/pass/quad/SQS admission and memoizes repeated child frames; its seed-only spec execution is unclassified pending an admitted self-hosted CLI.
- dev: Created state file with 12 acceptance criteria (type: code-quality); preserved the completed legacy `.spipe/mission_critical_harden` lane and isolated this broader Simple/SimpleOS/rendering/allocation goal as V2.
- research: User selected C1/O1/R2/M2/N2; final feature and NFR requirements written and option drafts removed.
- design: Architecture, detail design, system-test plan, and disjoint parallel-agent plan completed with frozen V1/V3 contract names.
- impl wave 1: Added pure-Simple compiler admission, scoped certified-SimpleOS manifest validation, packed DrawIR-v3 generation admission, sealed relaxed domain arenas, bounded process policy, and focused unit specs.
- impl review: Corrected certified-subset semantics so scoped O1 certification can pass without claiming all platforms; bound DrawIR plans to the originating arena identity.
- impl process-policy wave: Extended the pure V2 policy with explicit timeout and distinct max-in-flight admission, bounded capture boundaries, admitted/running/cancel-requested/timed-out/completed lifecycle receipts, deterministic invalid-transition rejection, and fail-closed PID validation before signal/wait intent. Unit/system traceability is labeled policy-only; real owner-facade process integration remains blocked and unclaimed.
- blocker: Focused specs cannot start because the pre-existing unresolved conflict in `src/compiler/70.backend/backend/runtime_compiler.spl` parses as `TripleLt`; the conflict belongs to another active session and was not modified or retried.
- impl wave 2: The external conflict cleared. Added canonical SHA-bound compiler/aggregate receipts, exact catalog/run/coordinate-bound SimpleOS evidence, DrawIR forged-plan/abort/terminal guards, committed-vs-staging arena isolation, frozen-profile detection, and bounded process timeout/cancellation/in-flight policy.
- focused evidence: SimpleOS manifest PASS 11/11; compiler admission FAIL 6/10; DrawIR arena FAIL 3/8. Third verify/fix cycle cap reached; remaining failures and resume commands recorded in `doc/08_tracking/bug/mission_critical_infra_hardening_v2_wave1_red_2026-08-11.md`.
- impl wave 3: Compiler admission PASS 10/10, DrawIR admission PASS 8/8, aggregate evidence PASS 7/7, bounded process policy PASS 12/12, and certified SimpleOS manifest PASS 13/13. The umbrella system scenario remained RED and full Engine2D/backend integration remained unclaimed.
- impl wave 4: Added allocate-once packed DrawIR-v3 slot storage with SHA-256 generation identity, bounded FIFO publication, queue saturation/retry, and completion-gated reuse. Added deterministic DomainArena pre-cursor/pre-publication fault injection; focused evidence reached 8/9 with telemetry persistence still RED.
- canonical baseline 2026-08-11: `scripts/check/check-simpleos-hardening-evidence-matrix.shs` failed closed with 9 stale reports (37-43 days old); retained log `/tmp/mci-v2-hardening-matrix-20260811.log`, SHA-256 `cd982a1142beb3cc1a51eb022d7a0d1eb4b849f265813c4a68d51b681280eb38`. The distinct `/tmp/simpleos-hardening-v2-baseline.out` is derived diagnostic output. No timestamp-only refresh or synthetic replacement was performed.
- impl wave 5: DomainArena deterministic fault telemetry PASS 9/9 after replacing an interpreter-broken `< u64::MAX` saturation guard with an equality-based non-wrapping sentinel check. Added canonical packed-generation Engine2D owner preflight/consume/release with durable-field identity binding; first focused run exposed a geometry/paint hash omission (1/2), fixed afterward without overclaiming GPU evidence. Split the umbrella system scenario into three owner-specific examples after three source-location-free runner failures; the next fresh focused run can identify the remaining owner by example title.
- authoritative prerequisites 2026-08-11: `check-simpleos-mission-critical-prereqs.shs` PASS (`sby`, `yosys`, and SMT solver ready). Compiler provenance `--probe` FAIL: deployed `bin/simple` is HYBRID/Rust-seed lineage, stage3 is missing, and `build/redeploy_out/simple_stage2` fails 3/9 current-source marker checks. Retained log `/tmp/mci-v2-compiler-provenance-20260811.log`.
- impl wave 6: Packed DrawIR Engine2D owner focused spec PASS 2/2 and source check PASS; evidence is CPU owner identity/consume/release only. Routed all 9 stale reports to exact producers/prerequisites; the safe GUI/RenderDoc producer regenerated a current FAIL report (`missing-behavior-evidence`), and the LLVM dossier still lacks a canonical producer. Umbrella test launch did not reach execution in 3 bounded attempts because whole-repo bootstrap-seed compilation exceeded the command bridge window; 3 examples declared, 0 executed, so no assertion was weakened or subsystem marked PASS.
- compiler recovery wave: Measured runner startup disproved the prior launch-time hypothesis (tiny 0.42s/70,888 KiB; umbrella 0.74s/77,568 KiB). Umbrella executes 2/3 and exposes interpreter cross-module mutation clobber after DrawIR retirement. An isolated no-stub Stage3 probe with admitted HYBRID/pure-Simple-bearing Stage2 completed 573-file closure and 837-module parse, then faulted on nil receiver before objects (71.00s, 3,264,060 KiB RSS). Three cache-preserving compatibility cycles fixed two semantics-neutral physical-line grammar sites and identified/fixed a third GPU-protocol split boolean without rerunning the capped build. Stage3 remains absent and no artifact is admitted.
- compiler recovery wave 2: Diagnostics localized the Stage3 nil trap to `module_surface_explicit_import_origin` reading a nil tagged-i64 position from the compatibility Dict. The pure-Simple export-origin index now scans authoritative aligned scalar arrays; adjacent replacement/no-duplicate regression added, not rerun after the three-cycle cap. A faithful umbrella minimization proves DrawIR `retire()` returns true but loses receiver mutation only under the combined import/declaration closure (new regression 0/2); subsequent arena/process calls are not causal. SimpleOS host-GPU protocol fixtures were updated from stale v1 to canonical v2 with prior/future rejection coverage; focused contract spec PASS 12/12, without claiming hardware evidence.
- compiler recovery wave 3: Export-origin index focused regression PASS 6/6. Re-running Stage3 with admitted candidate `268cd1fe...61cc` still faults at the same old instruction after 837-module parse (2:08.19, 3,259,716 KiB RSS, zero objects), proving that pre-fix Stage2 cannot validate its own compiler-owner repair; current Stage2 must be rebuilt first. The DrawIR mutation loss reduces to importing only DrawIR arena + DomainArena; process policy is unnecessary, and the only critical mutable-field collision is bare `next_generation`, implicating interpreter field/frame metadata but not yet proving an owner edit. Current storage formal producer PASS with hash-bound DB/FAT32/NVFS log; scope remains formal-model only.
- compiler recovery wave 4: Isolated exact-current Stage2 rebuild failed closed after 71.51s/365,116 KiB RSS with zero objects because the frozen Rust-seed Cranelift runtime table cannot resolve `rt_struct_receiver_valid` while lowering `vulkan_font_atlas_artifact_evidence`; pure-Simple and C runtime declarations exist, but the frozen native-all archive lacks the export. Receipt retained under `build/mini_builds/mission_critical_current_stage2_20260811/`. Further analysis disproved the earlier bare-field collision theory: cached field indices are receiver/name validated and method frames are declaration-scoped; seed mutation loss also occurs without DomainArena. No speculative interpreter patch landed. Current memory-safety formal producer PASS across 5 Lean projects/11 files/zero trust bypasses; model-only scope retained.
- runtime authority wave: Proved and repaired both missing layers for bounded struct receivers. `runtime_memory.c` now provides paired registered `rt_struct_alloc`, bounds-aware `rt_struct_receiver_valid`, and free-time invalidation; Cranelift `runtime_sffi.rs` has exact signatures/tier classification; canonical required/name manifests include both symbols; historical focused C fixture restored. `-Wall -Wextra -Werror` compile, archive `nm`, linked bounds/post-free selfcheck, and focused common crate build PASS; the attempted Rust test filters executed 0 tests, so no unit assertion execution is claimed. DrawIR mutation investigation now points to helper-returned receiver copy semantics rather than import/name collision; a dedicated local-control/helper-return regression was added but cannot execute until bootstrap/runtime recovery.
- authority tuple wave: Correct Rust `simple-compiler` registration test executed and PASS (1 test, 8 allocator/validator signature+tier assertions, 0 failures). Full private seed/native-all tuple build was boundedly interrupted during first `simple-compiler` compile after 3:57.39/998,744 KiB RSS with 52 private objects; input manifest remained stable, no tuple or Stage2 artifact exists, and private target is retained for cache-preserving continuation. Current critical-concurrency formal producer PASS once (85 theorems, 5 Lake projects, 14 files, zero trust bypasses), model-only scope retained.
- authority tuple wave 2: Cache-preserving private seed build completed PASS after 8:24.57/2,525,348 KiB RSS, SHA `92482953...5cf2`, with frozen 9-file manifest stable at `fdecfa6c...227d`. Its static runtime archive contains both struct allocator/validator symbols, but the final seed exports only `rt_struct_alloc`; `rt_struct_receiver_valid` is absent from static/dynamic seed symbols, so tuple admission remains RED and native-all/Stage2 were not started. Concurrent runtime selfcheck PASS 1,033 assertions including 1,024 ordered post-free rejections. Current CPU/SIMD producer FAIL (`simple-bin-simd-smoke-failed`) because release candidate `04a38e...e0` segfaulted before bitmap/facade execution; no parity claim advanced.
- authority tuple wave 3: Corrected admission model: JIT uses generated `RuntimeSymbolProvider` before dlsym, so dynamic ELF export is not required. Root cause was runtime `build.rs` scanning only single-line C definitions; the multiline validator was absent from generated registration and link-GC'd. Added shared top-level multiline C-definition scanner plus regressions: scanner PASS 1/1 and paired provider/bounds behavior PASS 1/1; generated table and test static symbols contain allocator+validator. Full seed/native-all rebuild remains pending. CPU/SIMD segfault localized pre-SIMD to stale candidate array-length lowering in `startup_normalize_program_args` (tagged nil args dereferenced); existing report remains FAIL and no SIMD edit landed.
- authority tuple wave 4: Cache-preserving private seed rebuilt successfully with scanner fix (9:55.02, 2,530,528 KiB RSS, SHA `afc6f97f...1ac4`); frozen critical manifest stayed byte-identical, generated provider table contains both struct rows, and final seed static symbols retain allocator+validator. Independent review PASSes the repaired current path but warns scanner is not a general C parser for macro-generated definitions/preprocessor/string brace cases; no broad claim made. Native-all and Stage2 remain pending. Exact Stage2 contract requires a fresh exact-current immutable source snapshot; old `977c...` bundle must not be reused.
- authority tuple wave 5: Cache-preserving native-all/backfill build was boundedly interrupted while compiling native-all, leaving 1,011 private objects. Seed remains SHA `afc6f97f...1ac4`; compiler-backfill completed SHA `b82a4989...a07a`; native-all absent, so tuple admission/Stage2 did not start. Exact-current source snapshot attempt correctly rejected concurrent drift (snapshot 11,860 files/SHA `bc8136...f3b`, live after 11,861/SHA `8ad4c5...c2b`); no unstable snapshot promoted. Diagnostic private-seed receiver tests failed to reach execution and one exceeded ~3 GiB RSS, so no interpreter patch/claim.
- authority tuple wave 6: Matching private native-all/backfill build and admission PASS (9:03.81, 2,526,976 KiB RSS). Frozen read-only tuple hashes: seed `afc6f97f...1ac4`, backfill `07deec4f...67f`, native-all `416a3e7c...f64c`; regular/non-symlink, SHA sums revalidated, allocator+validator exact definitions present, generated provider rows present, linked provider/bounds regression PASS 1/1, 9-input stability PASS. Exact-current read-only Stage2 source snapshot admitted on attempt 3: 11,862 files, SHA `f75d6123...e1c331`, stable HEAD/dirty identity; earlier drifted attempts rejected. RISC-V dual-track producer FAILed closed before proofs because canonical `bin/simple` remains Rust seed; no formal/hardware claim advanced.
- exact Stage2 wave 1: Hermetic env-i no-stub Cranelift build ran against admitted immutable source+authority and rejected in 10.76s/29,036 KiB before objects (cache 0/output absent) on ambiguous package export `LoopInfo` from vectorizer and loop detection. Independent launch and 11,862-file/authority immutability audits PASS. Fixed smallest live pure-Simple owner: package `mir_opt/__init__.spl` retains canonical loop-detection `LoopInfo` export and stops bare-reexporting vectorizer's distinct type; direct module consumers remain valid. Added exact+adjacent regression and bug record; focused static check PASS. Evidence frozen/hash-bound; a new stable source snapshot is required before retry.
- exact Stage2 wave 2 preparation: Independent resolver review proved the initial bare-export edit insufficient. Durable fix renamed vectorizer model to `VectorLoopInfo` across production/tests, leaving loop-detection `LoopInfo` the sole bare provider; strengthened package-resolution regression and focused check PASS, independent final review PASS. Snapshot capture then failed closed at 3 attempts: first copy-window drift; attempts 2/3 had stable 11,867-file SHA `239298...` but preserved two source `.spl` symlinks, violating the no-symlink criterion. No snapshot admitted or Stage2 retry run. Next capture must predeclare and evidence a canonical symlink-materialization rule.
- exact Stage2 wave 2: Replaced the invalid no-symlink rule with a reviewed symlink-preserving contract. Final snapshot admitted with 11,867 regular sources, 21 verified internal aliases, 17 explicit exclusions, and 540-file/2,453-edge bootstrap closure; live/copy proof differences were hash-bound and reviewed. Hermetic Cycle2 build PASS (818 compiled/0 failed, 19:05.86, 503,372 KiB RSS, SHA `7dbc3cf4...286b`, no stubs) but admission FAILed immediately on `--version` with invalid field receiver. GDB proved struct init/copy used raw `rt_alloc` while guarded field access requires registered `rt_struct_alloc`. Fixed paired Rust and pure-Simple Cranelift struct allocation paths; Rust regression PASS 2/2. Added pure-Simple Get/SetField pre-dereference validator/trap path (focused result obscured, no PASS claim). Runtime transient scope now reclaims via canonical `rt_free`; strict C regression PASS including stale rejection and 256 ordered cross-thread rounds. Cycle2 artifact remains diagnostic-only and cannot run Stage3.
- overwrite recovery wave: Concurrent HEAD advance erased several proven fixes; authority/source rebuild was held before launch. Restored and rechecked durable `VectorLoopInfo`, pure-Simple struct allocation+field guards, and transient-scope canonical-free fixes (focused Simple and strict C tests PASS). Restored Rust runtime signature/manifests/multiline scanner/struct allocator files; scoped diff clean, but isolated focused compiler test was stopped during compilation at ~8m and is INCOMPLETE. Reconciled LLVM struct/class init and recursive aggregate copy to `rt_struct_alloc` while closure stays raw; initial focused test 3/4 due test self-scan, boundary corrected but not rerun. No authority-v2/source-v3 snapshot, Cycle3, or Stage3 claim exists.
- formal memory refresh 2026-08-11: `check-simpleos-memory-safety-formal-proofs.shs` PASS across five Lean projects (11 files, zero trust bypasses); retained log SHA-256 `c72caf9a01ae23fdac34560a452632170a0ee732fa4f6e281ce5968bcf7dd81b`. This advances the standalone modeled-property row only; native/codegen correspondence, concurrent execution, QEMU/hardware, aggregate, and release claims remain open.
- formal critical-concurrency refresh 2026-08-11: `check-simpleos-critical-formal-proofs.shs` PASS once with 85 required theorems across five Lake projects/14 Lean files and zero trust bypasses; retained log SHA-256 `bb14f78dd57aba33f354cdbd76ab2edce74abff246d3e17be6a94f7b7407e27a`. This advances only the scheduler/channel/DRF/capability formal-model row; native/runtime correspondence, deployed race freedom, QEMU/hardware, aggregate, and release claims remain open.
- CPU/SIMD refresh 2026-08-11: the canonical Engine2D evidence producer ran exactly once against explicit release candidate SHA-256 `04a38e21...b9e4e0` and failed closed before bitmap/facade execution because its required interpreter SIMD smoke segfaulted (`simple-bin-simd-smoke-failed`). Hash-bound report/log receipt: `build/cpu-simd-engine2d-evidence-20260811/receipt.md`. CPU/SIMD remains RED; no GPU, QEMU, aggregate, or release claim was advanced.
- RISC-V dual-track refresh 2026-08-11: `check-riscv-formal-dual-track.shs` ran exactly once and failed closed after its eight-fixture sidecar self-test passed because canonical selection resolved `bin/simple` to Rust bootstrap-seed SHA `df2da495...f5a0`. BYL/Lean checking did not begin. Hash-bound receipt: `build/evidence/mission_critical_infra_hardening_v2/riscv_dual_track_20260811/receipt.md`; log SHA `7057820a...ce381`. This is compiler-admission evidence only; formal dual-track, RTL/SBY, QEMU, FPGA, hardware, aggregate, and release rows remain RED.
- migrated baseline 2026-08-12: The canonical matrix was invoked once after moving the worktree to `/mnt/data/worktrees/simple-main`, with report/log output redirected to `/mnt/data/worktrees/`. It hit the 180-second bound before emitting a release verdict, so no PASS/FAIL summary is claimed. The completed preflight still reports nine stale checked-in evidence reports (38-44 days old); retained diagnostic log `/mnt/data/worktrees/mci-v2-hardening-matrix-20260812.log`. No timestamp-only refresh, cached substitution, or hardware promotion was performed.
- traceability hardening 2026-08-12: Scenario classification parsing now validates every `@scenario` declaration and rejects absent or punctuation-only reasons. The focused traceability producer contract passed once, including both negative controls; this closes the previously observed `scenario without reason accepted` failure without promoting DOC-001/002 or fabricating docgen evidence.
- aggregate/release hardening 2026-08-12: Tooling archive inspection now caps member/expanded-manifest limits and requires exactly one canonical manifest. The release orchestrator requires the candidate aggregate's exact blocked status/report and byte-identical final compatibility report. Focused aggregate and controlled release-orchestrator contracts passed once; the live release remains blocked on real lane evidence, external signing, reviewer operation, and incomplete compiler/external-host rows.
- compiler producer hardening 2026-08-12: Required CLI values are validated independently and both compiler evidence/template collisions fail closed without overwriting prior output. Shell syntax and diff checks passed, but the bounded focused campaign emitted no PASS marker and was not rerun. COMP-002/003, NFR-003/004, independent cross-host evidence, and live trust provisioning remain blocked.
- stale-report routing 2026-08-12: The hardening matrix now resolves newest same-prefix reports by embedded ISO date rather than lexical filename order, retains filename-age rejection, and emits an explicit classification/resume map for all nine stale families. Five are current-host executable only after their named prerequisites; LLVM lacks a canonical producer; GUI/RenderDoc, production parity, and QEMU GTK remain external-hardware blocked. No report was regenerated or promoted.
- docgen provenance audit 2026-08-12: Corrected the DOC owner to `src/app/spipe_docgen/main.spl` and removed the obsolete runtime-compiler-conflict resume wording. Focused traceability contract passed with a clearly synthetic receipt fixture. Static audit then proved the actual docgen owner does not emit `mci-spipe-docgen-provenance-v1`; filed `doc/08_tracking/bug/mci_v2_docgen_provenance_receipt_not_emitted_2026-08-12.md`. DOC-001/002 remain blocked on implementing binary-bound receipt emission plus admitting an exact-current self-hosted CLI.
- compiler campaign diagnosis 2026-08-12: Batched source-manifest hashing and collision/argument guards are present, but the one post-fix controlled run still emitted no PASS. Its retained log shows the outer bounded test terminated while a child snapshot copy continued, after which trap cleanup removed destination parents and the child reported `source-aba-or-input-mutation`. This is inconclusive controlled-contract evidence, not compiler failure or cross-host evidence; no rerun was performed.
- docgen provenance implementation 2026-08-12: Added canonical `--provenance-receipt` ownership in `src/app/spipe_docgen/spipe_docgen/main.spl`, exact ordered `mci-spipe-docgen-provenance-v2` serialization, binary/spec/manual SHA-256 binding, input revalidation, and atomic post-success publication. The traceability gate now snapshots and hashes the claimed executable and rejects mutated binary fixtures. Focused traceability negatives PASS; the direct receipt-writer integration spec PASSed 5/5 on the Rust seed as diagnostic evidence only. A direct `bin/simple spipe-docgen ...` diagnostic still received no usable delegated argv and returned usage; bug `spipe_docgen_file_delegation_drops_cli_args_2026-08-12.md` records the blocker. No real receipt was fabricated; DOC-001/002 remain blocked on delegated argv repair and an admitted exact-current pure-Simple run.
- compiler timeout containment 2026-08-12: Compiler snapshot/build children now run in bounded process groups with TERM/grace/KILL/wait cleanup, preventing orphan copies after timeout. Shell syntax and diff checks passed. The single focused contract exited 1 with suppressed diagnostics; static diagnosis points to a pre-existing absolute-vs-relative source-manifest fixture mismatch, so no compiler campaign or release evidence is claimed.
- shared-WM evidence refresh 2026-08-12: Canonical producer ran once and failed closed with `simple-bin-forbidden` because `bin/simple` is the Rust bootstrap seed. Report/manual now retain the exact admitted-self-hosted resume command and host-only scope; no GPU/QEMU evidence was claimed.
- delegated docgen argv repair 2026-08-12: Diagnosis proved the thin compatibility wrapper hid imported `rt_cli_get_args` use from the argument-sensitive execution selector, so JIT dropped delegated arguments. `src/app/spipe_docgen/main.spl` now owns real argument acquisition and removes only the file-delegation entry path before calling the canonical owner. The first bounded post-change command exposed that prefix and the correction landed at the three-cycle cap; final CLI verification remains pending. No receipt was fabricated.
- bounded cross-domain transport wave 2026-08-12: Added a versioned inline-only `TransferEnvelopeV1`, bounded 64-entry actor inbox/outbox channels, nonblocking scheduler backpressure with the global mailbox lock released before send, validated envelope decode, and actor-owned cloning of inline-only array contexts instead of passing caller heap pointers across threads. ABI review froze stricter future semantics for handles/leases and found broader Simple/C channel contract gaps. Implementation diff-check passed; no focused Rust test ran before checkpoint, so this is unverified and not release evidence.
- focused verification wave 2026-08-12: The canonical delegated docgen command ran once to a private `/mnt/data` output and PASSed, producing an exact 15-field v2 receipt whose executable/spec/manual hashes all matched; this remains Rust-seed diagnostic evidence, not release admission. Focused Rust transfer tests PASSed 3/3 (tampered/heap-tag envelope rejection, capacity+1 backpressure without growth, nested-heap actor context rejection). The compiler admission contract hit its fresh 120-second bound with status 124 and only `Terminated` in the retained log; it remains unverified and was not rerun.
- compiler contract convergence 2026-08-12: Reordered cheap negative controls ahead of source capture, replaced per-file snapshot shell loops with bounded bulk copy plus batched hashing, and retained process-group timeout cleanup. The focused controlled compiler-admission contract PASSed once in 13 seconds. This is contract evidence only; independent cross-host COMP-002/003 and NFR-003/004 evidence remains blocked.
- bounded channel/mailbox wave 2026-08-12: C and interpreter scalar channels now use fixed capacity and atomic nonblocking backpressure; the direct strict C runtime channel selfcheck PASSed and the focused Rust interpreter capacity+1 test PASSed. Actor/interpreter mailboxes no longer expose unlimited construction, clamp priority reserve to physical capacity, and correct stale/drop/byte accounting; focused Simple checks and stale-drop spec PASSed. The native Simple channel spec still fails because native test execution resolves the incompatible unbounded Rust `rt_channel_*` object ABI first, while a separate cached AOT archive contains the old grow-on-full C object. ABI namespace/provider closure and the pre-existing interpreter mailbox static-method resolution failures remain explicit blockers.
- channel provider closure 2026-08-12: Renamed the Rust heap-object channel exports to `rt_value_channel_*`, leaving the scalar ID/status `rt_channel_*` namespace to the C runtime. Rust object channels now have fixed 1024-entry capacity, nonblocking full rejection, and FIFO drain-after-close semantics; focused runtime tests PASSed 9/9 and the Rust archive exports no colliding scalar names. Explicit `SIMPLE_SIMPLE_CORE_PATH`, `SIMPLE_CORE_RUNTIME_PATH`, builder runtime paths, and simple-core provider selection now reject archives older than their runtime sources; both focused override regressions PASSed. A fresh admitted self-hosted native Simple binary is still required before the prior native spec can become release evidence.
- transfer/mailbox contract hardening 2026-08-12: Process/remote object handles now require frozen-share mode with nonzero generation and ownership token, while inline and encoded-copy modes remain available. Fabricated/nonpositive shared-reference IDs reject and unavailable heaps no longer synthesize ID zero; focused Rust transfer tests PASSed 2/2. Interpreter mailbox bootstrap constructors were converted from duplicate mangled definitions to canonical static methods, resolving the prior 29 source-level method errors. Simple verification is currently blocked before these specs by the unrelated parser failure in `src/compiler/50.mir/verification_contract_bridge.spl`; the missing owner-scoped capability registry/revocation authority remains tracked and unclaimed.
- provider/race closure 2026-08-12: The compiler native concurrent provider now uses a fixed 1024-entry Crossbeam queue and nonblocking full/closed errors; focused provider tests PASSed 7/7. Rust object-channel lifecycle ownership is mutex-serialized across send/close/is-closed/free, removing the close/send use-after-free window while preserving drain-after-close; focused runtime tests PASSed 10/10. Renamed the Rust scalar-only record to `InlineValueEnvelopeV1` so the canonical domain/mode/ownership `TransferEnvelopeV1` has one unambiguous name; focused inline golden/tamper tests PASSed 2/2. Dynamic interpreter/compiler `Value` transport classification remains a separate P0 blocker.
- typed/time transport closure 2026-08-12: Interpreter and native compiler channel sends now recursively admit only scalars, strings/symbols, frozen arrays/dicts, and safe enum/union/unit payloads; mutable containers, opaque objects, handles, closures, and pointer-like values reject. Focused interpreter admission tests PASSed 3/3 and native provider tests PASSed 2/2. Interpreter mailbox/message-transfer/scheduler timestamps now use the monotonic runtime clock; receive-with-timeout is bounded, sleeps through the runtime facade, and closes as cancellation rather than returning a fabricated instant timeout. Source parsing passes, but focused Simple execution remains blocked by the unrelated `lean_backend.spl` parser failure, so runtime timeout evidence is not yet claimed.
- parser unblock wave 2026-08-12: Replaced unsupported multiline expression conditionals/pattern continuations in the untracked verification bridge/region owners; the focused region source check PASSed. Renamed reserved `invariant` binding in `lean_backend.spl` and recorded the parser regression. Three bounded mailbox executions successively exposed these unrelated compiler parse blockers; the final Lean source check timed out under concurrent workspace load, so the mailbox/transfer Simple runtime criteria were not rerun and remain unverified rather than promoted.
- capability/actor admission wave 2026-08-12: Added a fixed-capacity value-only object-handle registry that mints nonzero tokens, binds owner context/generation/boundary, consumes validation once, and supports owner-only revocation; its Simple spec is currently blocked by an unrelated `verification_ir.spl` parser failure. Added result-bearing actor send/reply ABI with explicit ACCEPTED/FULL/CLOSED/INVALID/CANCELLED outcomes while retaining legacy compatibility wrappers; focused runtime actor tests PASSed 31/31 and common actor tests PASSed 2/2. Compiler-wide check remains blocked by the unrelated existing `exec_function_with_self_value` import failure.
- high-model transport closure 2026-08-12: After Luna implementation lanes, two independent `gpt-5.6-sol` high-reasoning reviews found and drove fixes for object-channel free/use UAF, raw compiled `Any` admission, Native/PureStd result mismatch, fail-open mtime archive admission, actor handle registry omission, cached-archive identity bypass, and provider-manual overclaims. Current source uses Arc-held object-channel leases, classified scalar/typed-i64 C APIs, shared boolean provider semantics, SHA-256 source-tree+archive identities on fresh and cached paths, registered actor handles, and a public result hook. The regenerated 17-scenario/556-line manual has zero stubs and passed fresh high-model guide review. Final high-model verdict PASS applies only to this host-independent HOLD-fix scope; admitted self-hosted/native/separate-process evidence and runtime capability-registry integration remain blocked and unclaimed.
- real arena backing wave 2026-08-12: Added two constructor-preallocated storage-bank objects, scalar staging writes, committed-only scalar reads, exact minted-span tables, rollback byte/ref/fault clearing, and byte-inclusive evidence hashing. Focused source check PASSed. Three high-model review/fix cycles were consumed and the lane stops at HOLD: the exported V1 state-hash domain was changed incompatibly instead of versioned; class-reference/struct-in-class semantics lack interpreter/native parity evidence; owner-confined metadata+selector publication is not type-enforced atomic for concurrent readers; and extreme quota/ref capacity admission is not yet robust. Allocation producer compatibility and production callers remain blocked; no MCI allocation PASS is claimed.
- docgen provenance host check 2026-08-12: No admitted exact-current pure-Simple runner is present (`bin/simple` is the Rust bootstrap seed). The focused MCI traceability contract ran once and PASSed with only synthetic hash-bound receipt fixtures; retained log `/mnt/data/mci-docgen-traceability-contract-20260812-run2.log`. DOC-001/002 remain HOLD with no live receipt fabricated. Corrected the stale duplicated SimpleOS manifest sentence in the hand-maintained operator mirror; owner/reason/resume metadata remains aligned with the executable scenario matrix.
- evidence-wrapper review wave 2026-08-12: Tooling-v3, SimpleOS 26/26 binding, and the SimpleOS collector each consumed their bounded implementation/review cycles and remain HOLD. Tooling retains raw samples and producer-side recomputation but signer/aggregate semantic recomputation, exact scan telemetry, and coherent baseline evidence remain incomplete. The 26/26 release gate has stronger SHA/revalidation wiring but aggregate enforcement is optional, exact decimal ordering is incomplete, and ordering/mutation coverage is stale. The collector fixture is non-promotable, but live evidence remains host-self-attested and producer/consumer fields are incompatible; no QEMU/guest or 24-hour release claim is made.
- packed DrawIR production-owner wave 2026-08-12: Added a partial shared owner bridge, strict RECT semantic rejection, WM refusal-only fallback, and an explicit `SEALED -> QUEUED -> IN_FLIGHT -> FREE` lifecycle; repaired malformed abort/reuse test scope. Three high-model cycles ended HOLD: canonical v2 batches still introduce rejected GROUP commands, hosted Web bypasses the bridge, admission still constructs growable scenes/identity rows and hashes/copies during an active generation, and owner capability confinement is absent. Docs now identify this as a partial prototype rather than production evidence.
- owned-process cancellation wave 2026-08-12: Internal runtime cancellation now records a request under the owner lock and the runner performs TERM/grace/KILL/exact reap; invalid ABI inputs return initialized receipts and focused C core/adapter/non-Unix checks PASS. Three high-model cycles ended HOLD because the public Simple API remains synchronous and returns a stale receipt, no opaque owner-bound async handle exists, escaped descendants are not contained, and native Simple/source-matched executable evidence is absent. Unsafe cross-thread receipt probing was removed and docs no longer claim a usable public async capability.
- compiler parser blocker 2026-08-12: `bin/simple check src/compiler/50.mir/verification_ir.spl` passes alone, but a full compiler closure still fails parsing an implementation-body local `var` (`expected Fn, found Var`). The bounded lane removed misleading loop suspects and stopped without normalizing valid source or claiming the capability-registry Simple spec executed.
- bootstrap parser parity fix 2026-08-12: Highest-tier diagnosis proved the full-closure `expected Fn, found Var` error was Rust bootstrap pseudo-indent debt after a trailing-operator multiline condition with an inline `if` body; the current pure-Simple lexer was already correct. The Rust inline-if owner now uses the established credit-bounded dedent reconciler, focused Rust parser tests PASS 10/10, and exact/adjacent pure parser parity scenarios were added. This fixes bootstrap parsing source but does not itself admit a self-hosted compiler.
- compiler authority blocker wave 2026-08-12: Retained Stage2 receipts still fail sanity status 132 (`invalid_field_receiver`). A proposed type-only Cranelift guard was removed after high review showed erased named-struct results and raw tuple/fat-pointer receivers are indistinguishable without explicit MIR field-receiver provenance. The required future change must thread provenance through GetField/SetField constructors, rewrites, serialization, interpreter, and backends; no causal Stage2 fix is claimed.
- MIR Infer lowering wave 2026-08-12: Scalar folded inferred constants now derive optional MIR types, mutable folded binary statics retain numeric type, explicit widths remain authoritative, and unresolved zero/aggregate values record fatal errors. Flat and entry bootstrap paths reject fatal MIR errors. Three review cycles ended HOLD because `bootstrap_lower_extra_hir_module_to_mir_for_target` still discards those fatal diagnostics and unsupported/bootstrap negatives remain structural; aggregate-producer admission is not claimed.
- DomainArena V2 experiment 2026-08-12: Added a separate fixed-bank byte/span/mint prototype and restored the exported V1 state-hash canonical domain. Three high-model cycles ended HOLD: underscore helpers are not private in Simple, capability/checkpoint values remain forgeable, the exported mutable arena cannot enforce its documented non-Send/owner-only boundary or atomic publication, and profile/capacity fields remain externally mutable. V2 is experimental and unwired; no allocation evidence is promoted.
- direct-native module initialization fix 2026-08-12: Unix direct-native startup now discovers both bare `__module_init` and prefixed module initializers, excludes the wrapper-owned dynamic helper, sorts/deduplicates symbols, and invokes each weak initializer once before user entry. Highest-tier static review PASSed the scoped Unix fix; focused Cargo execution was not retained, and Windows/MSVC behavior remains unproven.
- parallel ownership integration wave 2026-08-12: Added typed interpreter mailbox packets with bounded accounting and one-shot owner-scoped handle consume/revoke, result-bearing `ActorSend(dest, actor, message)` through Rust and Simple MIR/native emitters, and a scalar eleven-word structured lifecycle/task-group codec with exact owner snapshot comparison, cancellation/join/free, and deterministic parent commit. Highest-tier review drove cleanup of stale two-field MIR matches, SSA dest/use accounting, fabricated interpreter success, silently erased LLVM sends, packet-kind confusion, typed queue accounting, and overstated requirement traceability. Current static source consistency PASS applies only to those repaired points; scheduler/mailbox end-to-end capability tests, ActorSend cross-backend execution, lifecycle scenario execution, real traps, process isolation, and a single cross-language transport remain HOLD.
- focused parallel runtime evidence 2026-08-12: Result-bearing ActorSend Rust-seed Cranelift AOT/SSA focused test PASS 1/1; this proves compilation and result preservation, not the five runtime admission statuses. The canonical native C channel lifecycle gate PASSed on pthread, covering >64 generation-stamped slot reuse, stale-handle rejection, close/drain, concurrent free, blocked-receiver quiescence, and replacement isolation. Cross-runtime channel parity and source-level ActorSend behavior remain HOLD. Unix direct-native bare/prefixed module-init discovery has highest-tier static PASS; its focused test reached a formatting-sensitive assertion, corrected afterward without rerun, so executable test status remains HOLD.
- actor/channel runtime evidence 2026-08-12: The real Rust actor provider focused test PASSed all five stable outcomes (`ACCEPTED`, `FULL`, `CLOSED`, `INVALID`, `CANCELLED`) and was hardened to use explicit lifecycle barriers instead of sleeps. The C scalar channel lifecycle gate PASSed with generation-safe free/reuse and blocked-receiver isolation. Interpreter scalar admission was narrowed to the native signed-61-bit range with boundary tests, but its isolated Cargo execution was interrupted during a long final compiler build; cross-runtime parity remains HOLD.
- canonical object-handle authority 2026-08-12: C and Rust runtime gates PASSed for OS-CSPRNG bearer owner/token issuance, tuple-bound mint/consume/revoke, replay/wrong-owner/target/generation/region rejection, capacity, consume-vs-revoke, owner destruction, destroy-vs-consume, and >64 owner slot reuse. ActorScheduler now uses this native authority and destroys/recreates its owner on stop/start. Simple execution remains blocked by the stale bootstrap parser; bearer leakage transfers authority by design.
- SimpleOS/QEMU host-owner foundation 2026-08-12: Added a typed six-ISA guest-evidence request contract and model-only VM lifecycle state machine, plus a fixture-only closed guest-command wrapper. Highest-tier review rejected the wrapper as a live owner and identified the canonical reuse plan: extend `_QemuRunner` descriptor/catalog, owned process lease, QMP client, scenario disk owner, and SOSIX serial parser. No live QEMU/SSH/accelerator evidence is claimed. The scheduler closure-port remains model-only with server capability false pending a real stack lease/TCB trampoline/terminal callback owner.
- rendering collector/adapter instrumentation 2026-08-12: Host-only collector, strict `mci-rendering-raw-v1` writer, semantic 17-row adapter, and fixture collector->adapter->checker contracts PASS without GPU. Production source now emits canonical composition/Web bytes, independent CPU/device captures, packed counts, interactions, latency/RSS, queue/submit/fence identifiers, fallback/DrawIR streams, actual-host-store capacity+1 refusal snapshots, and transient-owner inventory. Remaining HOLD: no Simple compile/GPU run, GUI/Web runtime parity is not live-proven, and the packed store preflight is not the exact generation sealed/published/consumed by the advanced frame renderer.
- PostgreSQL scalar worker foundations 2026-08-12: Canonical C gates PASS for generation/family descriptor and limits registries, scalar dispatch requests, out-of-order owner claims, immutable completion blobs, startup/config copied text identities, result rendezvous, and claim-bound adapters. An experimental gate-free scalar frontend/parent owner facade source contract PASSed. Highest-tier review keeps production HOLD: the live server still uses aggregate registries; startup publication and claim abort/release have races/leaks; completion ordering/destructive take is unsafe; blob bounds/per-byte hashing are unsuitable; cancellation lacks BackendKeyData semantics; and interpreter/native handle families differ.
- async identity-owned process lease wave 2026-08-12: Added v2 runtime-only opaque random-token start/poll/wait/cancel/result/collect with per-slot locking/op refs, deadline-clamped driving, combined capture budget, group TERM/KILL/exact reap, collision checks, hidden PID identity, and non-Linux refusal. Multiple strict selfchecks exposed lifecycle defects; the latest run accepts cancel then rejects subsequent poll, so terminal observation/collection semantics remain broken. No Simple/compiler ABI bridge or release evidence is claimed.

## 2026-08-12 compiler evidence, firmware lineage, and cache durability wave

- SOSIX collector self-test completed PASS after its detached session was recovered.
- Compiler-in-filesystem evidence now uses one closed 24-cell TSV policy across Unix and PowerShell owners. Live non-designated claims fail closed; controlled fixture evidence is BLOCKED/nonpromotable; mutation and symlink/hardlink alias checks were added. Producer source coverage was present, but no post-fix focused producer PASS was retained. Collector/parity final completion was not observable after the combined runner detached, so the lane remained HOLD pending bounded verification.
- Firmware transcripts now use one producer/collector validator requiring exact unique ordered stages and a unique nonce before guest entry. Collector contract PASS. Producer verification remains HOLD because its capped run intersected the concurrent compiler-designation fixture migration; the fixture was corrected afterward but not rerun.
- Native object-cache hardening now uses parent-authoritative publication, content-addressed private objects, same-directory temp/fsync/rename/directory-sync barriers, persisted digest/format/target scope, canonical containment, and hit-time structural validation. The corrected gate was not rerun after its final stale assertion fix, and the executable owner spec remains blocked by the unrelated verification_ir.spl parser failure. No durability PASS is claimed.
- Final `git diff --check` and generated-spec layout check passed.

## 2026-08-12 continuation: closed policy parity and durability authority

- Compiler designation now has one canonical 24-cell TSV plus one shared PowerShell parser/dump module. Both PowerShell consumers use it, and parity byte-compares both evaluated decision sets and exercises malformed/duplicate/missing policy rejection. Highest-tier static review PASS; native execution is honestly BLOCKED because `pwsh` is absent.
- The producer firmware contract no longer accidentally re-enables fixture designation for its live-policy negative. It has reachability receipts for missing/reversed/duplicate/nonce-after-entry sabotage. Syntax PASS; executable producer criterion remains HOLD pending a fresh session.
- Native object-cache static preflights now pass and the gate reaches the real owner spec. Execution stops on a stale deployed parser binary at `verification_ir.spl` (`expected Fn, found Var`). Source diagnosis ties this to the already-fixed Rust continuation/dedent parser bug; authoritative unblock is a full bootstrap/deploy, deferred because concurrent native builds/QEMU are active and root free space is below the project's 250 GiB heavy-build threshold.
- Cache production hardening now uses content-addressed private publication, temp/fsync/rename/directory barriers, exact digest/format/target metadata, canonical containment, and parent-authoritative serialization. Runtime proof remains HOLD until the deployed pure-Simple compiler is rebuilt and the real owner/kill-restart criteria execute.
- Final diff and generated-spec layout hygiene passed again.

## 2026-08-12 continuation: bounded GC and sealed rendering identity

- Bounded pure-GC runtime now has scalar owner/authenticated generation handles, safe i64 packing, cross-owner and forged-handle rejection, lazy single-domain default ownership, and lifecycle counters. Highest-tier static review PASS for that deliberately nonconcurrent/non-hosted-GC contract. Its interpreter spec is HOLD until the deployed pure-Simple CLI is rebuilt past the known parser defect.
- Rendering packed-generation evidence now retains a canonical immutable in-flight identity snapshot and independently verifies it in the adapter. Final static review PASS after adding pre-completion store revalidation, fail-closed poison on mutation/replay/reorder, GPU receipt validation while in-flight, and canonical raw-row rejection. Writer/source/bundle contracts PASS; compiled Simple and GPU evidence remain HOLD.
- SimpleOS compiler-in-filesystem collector now semantically validates hash-imported compiler receipts and rejects rehashed forged identity/stdout. Collector contract PASS. Review found a live-shaped lineage contradiction: firmware globally required the run nonce once while compiler receipts correctly repeat it post-entry; active follow-up splits dedicated boot correlation from repeatable execution identity and will bind compiler payload/image lineage.
- Heavy bootstrap remains active under `/mnt/data/.simple/bootstrap/.../cycle7`; root has about 121 GiB free, below the project 250 GiB heavy-build admission threshold, so no competing rebuild was launched.

## 2026-08-13 continuation: typed SOSIX admission and bootstrap provenance

- SimpleOS compiler-placement lineage was expanded to conditional 9/13 artifact evidence, including boot marker, target `/usr/bin/simple` payload readback, seven required compiler/interpreter/loader paths, alias/manifest hashes, and repeatable execution identity. Producer and collector contracts pass; PowerShell static parity passes but native PowerShell execution remains blocked without `pwsh`.
- Typed Pure-Simple SOSIX matrix admission now parses and validates these fields and exact artifact counts, ties kernel/image/transcript/program/firmware identities to retained artifacts, rejects fixture compiler PASS and all-false-policy compiler lineage, and requires current-run receipt/nonce/media correlation before Unix publication. Unix matrix self-test PASS; PowerShell static parity PASS; focused Simple typed spec blocked by the unproven current CLI.
- Bootstrap Cycle7 audit: Stage2 admitted (SHA d656135a…2461), but Stage3 failed `runtime error: invalid field receiver`; no Stage3/Stage4 artifact or provenance exists. Current bin/simple is unproven relative to Cycle7. A new clean /mnt/data campaign must wait for the receiver fix, writer quiescence, and the heavy-build admission threshold; no deployment was attempted.

## 2026-08-13 continuation: strict collector record and trusted importer

- Collector admission output now has a strict canonical 41-scalar plus exact 9/13-artifact record schema. Structural parser rejects duplicate, reordered, padded-index, noncanonical-decimal, oversized, and field-padded records. The collector contract passed before the last trusted-importer change; the latest two contract processes completed their negative suites and cleaned temporary roots, but their launcher lost terminal session IDs, so their final status is intentionally unclassified.
- Trusted SOSIX import now snapshots the closed 24-row matrix wire, resolves only canonical no-follow admission files under the collector root, hashes exact bytes against manifest values, cross-binds all canonical identity fields, and keeps structural parsing separate from root-bound release admission. Latest implementation is syntax/diff clean but still needs one fresh focused collector verification plus high-tier static review of the root-only release gate.

## 2026-08-12 SimpleOS compiler evidence lane closure

- The bounded `check-collect-sosix-qemu-evidence.shs` contract completed PASS.
  It verifies all 24 cells, canonical policy lookup, fixture-only conversion
  to `status=blocked`, retained compiler artifact hashes, designation
  tampering, firmware ordering/nonce negatives, lineage, and missing/duplicate
  bundle failures. No fixture row is release-admissible.
- The static Unix/PowerShell parity gate completed its available checks PASS
  and reported `BLOCKED` only for the environment fact that `pwsh` is absent;
  no PowerShell execution PASS was inferred. The policy remains 24 cells,
  all `false`, so no live compiler-in-filesystem claim is currently possible.
- Added the operator guide
  `doc/07_guide/platform/simpleos_compiler_in_filesystem_evidence.md` and
  indexed it from `doc/07_guide/README.md`. The guide records the exact
  producer/collector boundary, controlled-fixture nonpromotion, and the
  PowerShell environment limitation. REQ-SQ-008 remains open for real
  target-native guest execution and is not promoted by this contract PASS.

## 2026-08-12 compiler receipt semantic-correlation follow-up

- The earlier producer wording is normalized to **HOLD**: no post-fix focused
  producer PASS was retained, and PowerShell execution remains unavailable on
  this host. The recorded collector contract PASS is narrower than producer or
  live guest admission.
- The collector now validates the closed compiler receipt protocol after byte
  hashing: canonical receipt names, row host/guest/run nonce, mounted
  `/usr/bin/simple`, canonical hello paths, zero exits, target-native markers,
  nonce-bound stdout, and exact unique inclusion in the retained transcript.
  Rehashed wrong-row and forged-stdout negatives were added. This is
  host-independent contract hardening only; all 24 live policy cells remain
  `false`, Windows receipt production remains open, and no REQ-SQ-008 or
  release claim is promoted.
- The native bundle design now documents conditional 9/11 artifact counts and
  the semantic collector boundary. Focused execution evidence is recorded
  separately after the bounded checks; missing external Windows/QEMU evidence
  remains HOLD.
- Focused host-independent collector verification used two bounded cycles: the
  first exposed a review-only source-copy TOCTOU, semantic validation was moved
  onto the hash-verified retained copies, and the final run completed with
  `collect-sosix-qemu-evidence self-test: PASS`, including both rehashed
  semantic-forgery negatives. This closes the Unix collector contract only;
  producer, PowerShell/Windows, live QEMU, and REQ-SQ-008 remain HOLD.

- Pure GC owner lane 2026-08-12: Replaced `src/lib/gc_async_mut/pure/runtime.spl`
  content-hash/constant-stat placeholders with a bounded 64-slot owner heap.
  Allocations mint distinct slot+generation handles even for equal values;
  `get`, eager `dealloc`, deferred `release`+`collect`, stale-handle rejection,
  exhaustion, generation advancement, retirement-at-max-generation, and
  owner counters are implemented. Compatibility `alloc`/`dealloc`/`gc_collect`/
  `gc_stats` route through one module-owned runtime, while isolated callers can
  use `pure_gc_runtime_new`. A focused four-scenario spec was added. Source
  check passes; executable spec is HOLD because the deployed seed fails before
  execution on the unrelated stale `verification_ir.spl` parser (`expected Fn,
  found Var`). No native or production-wide GC claim is made. Design/manual
  contract: `doc/05_design/runtime/pure_gc_runtime_owner.md`.

- Pure GC authority repair/high review 2026-08-12: Highest-tier static review
  rejected the first bounded owner because a slot+generation handle from one
  runtime could authorize the same slot in another runtime, `GcHandle` was a
  mutable class bearer with an unused `RefCount`, and the declared generation
  maximum overflowed the 4096-stride signed-`i64` encoding. The implementation
  now makes `PureGcRuntime` the reference owner and `GcHandle` a scalar-only
  value bearer containing owner identity, generation-packed id, and a distinct
  per-allocation authorization checked against the live slot. `RefCount` is
  removed. The maximum generation is the signed-safe `0x7ffffffffffff`, and a
  final-generation release retires its slot. Lifecycle stats now distinguish
  live, pending-reclamation, retired, and available slots. Zero/negative
  capacity yields a closed zero-slot owner; oversize requests clamp to 64.
  Compatibility free functions use a lazy default owner rather than an unsafe
  module-global call-expression initializer. Owner/token minting and the
  default API are explicitly single-execution-domain and make no thread-safe or
  cryptographic-capability claim. The focused spec now has seven scenarios,
  including cross-owner/malformed rejection, scalar overflow arithmetic, and
  default-owner counter deltas; its mirrored manual is
  `doc/06_spec/01_unit/lib/gc_async_mut/pure_runtime_spec.md`. `git diff
  --check` passed. One focused `bin/simple test ... --mode=interpreter` attempt
  remained HOLD before executing the spec because the deployed compiler fails
  in the unrelated `src/compiler/50.mir/verification_ir.spl` parser (`expected
  Fn, found Var`). An earlier combined `check` invocation timed out in the
  repository checker and correctly rejected direct checking of an SSpec file;
  no execution PASS is inferred and no concurrency support is claimed.

## 2026-08-13 typed SOSIX admission repair checkpoint

- The typed collector-record parser now owns a bounded canonical grammar: 41
  exact ordered scalar keys and literal ordered 9/13 artifact path/hash pairs,
  with canonical decimal encoding and record/line size caps. PASS-row identity
  is derived from the parsed receipt. Parsing is named structural validation
  and no longer claims byte provenance; the collector manifest separately
  publishes the admission-record SHA-256.
- The latest focused collector invocation exited 1 because its new static
  bridge assertion hardcoded Linux/x86_64 as manifest row 2 even though sorted
  source paths place that cell later. The assertion now resolves the prefix by
  matching manifest host/guest fields, and the long-line assertion now really
  rejects lines over 8192 bytes. Per the bounded stop instruction, neither fix
  has been rerun. Current collector and typed runtime bridge status is **HOLD**
  pending one fresh-session focused execution; the older collector PASS does
  not verify these latest changes. PowerShell execution also remains HOLD.

## 2026-08-13 trusted SOSIX admission importer

- Added the narrow production `trusted_importer` owner. Its public evaluator
  accepts only a collector root, snapshots the ASCII matrix manifest, resolves
  canonical row paths beneath that root, rejects symlink/path escape, hashes
  the exact admission bytes against the manifest's admission-record SHA-256,
  parses those same bytes, and internally constructs typed rows. The former
  raw PASS-row factory is now explicitly structural and is not the production
  trust surface. Stale re-exports were corrected.
- The collector harness now has a source-static integration gate for no-follow
  path checks, canonical resolution, exact-byte SHA-256 binding, same-byte
  parsing, and the absence of the old trusted-sounding raw factory. A manifest
  descriptor scenario was added to the Simple spec. No Simple execution claim
  is made because the deployed compiler is stale; typed runtime admission and
  PowerShell remain **HOLD** pending current-toolchain execution.

## 2026-08-13 trusted importer type and non-PASS correction

- The collector manifest is now parsed as one closed ordered wire: two headers,
  24 sequential 42-field descriptors, and one bundle ID. Exact keys/order/count,
  canonical host/guest/status/boolean/decimal/hash fields, canonical base64,
  unique cells, and cell-relative evidence/admission paths fail closed. PASS
  remains restricted to canonical 9/13 artifacts; retained non-PASS receipts
  preserve their canonical 1–13 artifact sets without fabricated padding.
- Trusted import now byte-binds and cross-checks all 24 records, including
  BLOCKED/FAILED/UNSUPPORTED reason, resume, ownership, evidence, compiler, and
  artifact-count fields. Production evaluation returns the distinct
  `SosixQemuTrustedMatrixResult`; its module-private capability is required by
  the release-admissibility function. Raw structural parsing/evaluation remains
  directly available for unit tests but is not re-exported by the package
  admission surface and cannot satisfy the trusted release gate.
- The source harness covers the closed schema, beneath-root/no-follow checks,
  exact-byte hash and same-byte parse, non-PASS import, sealed trusted result,
  release gate, and structural-export exclusion. The descriptor scenario adds
  duplicate-hash, noncanonical-host, and BLOCKED-preservation negatives.
  Filesystem behavioral negatives and all Simple/PowerShell execution remain
  **HOLD** pending a current self-hosted compiler; source checks must not be
  reported as runtime admission PASS.

## 2026-08-13 root-owned release gate and complete field binding

- Removed the public mutable trusted result/capability path. The only release
  gate now accepts a collector root, performs trusted import and evaluation
  internally, and returns a boolean for the exact all-24-PASS result. The
  internal result type and evaluator are file-private; package exports expose
  neither them nor structural row/result/evaluator construction.
- All 42 manifest row fields are now consumed consistently. Every base64 field
  is canonical-decoded, and source/compiler lineage, kernel/image, QEMU,
  accelerator, firmware, nonce, transcript, program, ownership, status/reason,
  policy, path, hash, and artifact-count fields are cross-bound to the same
  admission bytes whose SHA-256 is pinned by the manifest.
- The shell collector fixture now behaviorally compares every emitted
  Linux/x86_64 manifest field to its admission record and verifies canonical
  base64 plus the record hash. Static forgery checks require the root-only gate
  and absence of public trusted-result or raw structural evaluator exports.
  This remains host-side source/collector contract evidence only; Simple
  runtime, symlink-race behavioral negatives, and PowerShell execution remain
  **HOLD**.
## 2026-08-13 verified trusted SOSIX admission boundary

- Fresh `sh scripts/check/check-collect-sosix-qemu-evidence.shs` completed `PASS` with terminal status retained after the strict record/root-importer changes.
- Highest-tier source review PASS: the public release surface is root-to-boolean only; closed 24-cell manifest rows and exact retained admission bytes are SHA-256-bound, every identity is cross-bound to the same parsed record, and non-PASS rows remain blocking. Structural text parsing is not exported as a release capability.
- Remaining evidence is intentionally separate: no current admitted self-hosted Simple importer execution; no `pwsh` host; policy remains all false with no live target-native compiler media/guest execution; bootstrap Cycle7 lacks Stage3/Stage4 after its invalid-field-receiver failure.

## 2026-08-13 immutable fn receiver ABI repair

- Cycle7's invalid-field-receiver root cause is a split ABI between Rust aggregate-method parsing, import discovery, and Cranelift receiver dispatch. The repair makes ordinary non-static aggregate `fn` methods synthesize immutable `self` (including trait methods), makes import arity consume parser-owned ABI parameters, and rejects undersized callee ABI before argument adaptation could hide a lost receiver.
- Focused evidence: Rust parser zero-arg immutable receiver regression PASS; import arity PASS; local and cross-module receiver behavior PASS. The ABI-underflow implementation emits a precise mismatch and returns the aggregate fail-closed compilation error; its assertion was aligned without rerun. No `me` workaround or bootstrap/deployment claim was made.
- Remaining bootstrap evidence: Cycle7 Stage3/Stage4 remain absent; a new clean campaign must still await high-tier review, source quiescence, and fresh lineage controls. Cycle8's later SIGSEGV remains a distinct blocker.

## 2026-08-13 targeted receiver ABI evidence

- Post-metadata Rust evidence PASS: `cargo check -p simple-compiler`; import-arity 1/1; local/cross immutable receiver behavior; and cross-module receiver-slot underflow fail-closed. Core Cycle7 `CompileContext.fn has_errors()` path is statically repaired without converting queries to `me`.
- High-tier review keeps broader language-surface verification HOLD: parser/HIR disagreement remains for `me`, malformed `static fn` bodies containing self, and some enum/extend/impl/decorated static paths. Active follow-up makes parser receiver metadata the sole HIR authority and adds all-form controls before any bootstrap retry.

## 2026-08-13 receiver ABI metadata follow-up (unverified checkpoint)

- Higher-tier review found arity-only receiver dispatch was still unsafe and enum/extend paths lacked uniform immutable receiver synthesis. A bounded follow-up introduced explicit `FunctionReceiverKind` metadata from parser/import discovery through Cranelift, centralized non-static receiver synthesis across aggregate forms, and fail-closed receiver/arity validation. The change is a checkpoint only: dependent call sites/test fixtures remain to be reconciled and no Rust compile/test ran after the metadata migration. Do not use it for a bootstrap campaign yet.

## 2026-08-13 V1 relaxed-arena preconstruction bound (static checkpoint)

- `DomainArenaV1` remains a live mission-critical evidence path, so it now rejects a sealed profile above its finite 16 MiB quota before constructing either of its two backing banks. The fixed storage helper enforces the same bound as a defensive backstop.
- The V1 unit spec adds a sealed oversize-profile rejection with zero cursor mutation. Scoped `git diff --check` passed; executable Simple evidence remains HOLD pending the active provenance-bound self-host compiler campaign.

## 2026-08-13 SimpleOS exact formatted-output ownership

- `vasprintf` no longer publishes a fixed 4 KiB truncated buffer while returning the full would-be length. It measures with a copied `va_list`, checks allocation arithmetic, renders to exactly sized storage with a second copied list, and fails closed on a render disagreement.
- Focused host C harness passed normal and 5,014-byte output checks plus null-output rejection. Host glibc annotations emit three known nonnull-comparison warnings from unrelated extension compatibility functions; the harness otherwise uses `-Werror`.

## 2026-08-13 SimpleOS allocator split transaction closure

- Allocator split rollback now checks reinsertion of the former free node. Fresh-region remainder insertion either publishes its node or unregisters the newly mapped region and poisons subsequent allocations; it never leaves an unreturnable live allocation in tracked metadata. Any unrecoverable internal list failure is fail-closed for later allocation/free operations.
- A deterministic test-only insertion-failure hook exercises both restoration of an existing split block and fresh-region failure/poison behavior. The focused strict C transaction harness passed. The normal allocator safety harness passed earlier in this session before this error-path-only patch; it was not repeated under the per-criterion run cap.

## 2026-08-13 provenance-isolated Stage2 campaign failure

- The `perf-stage2-f96fe5b37fd-20260813` Cranelift campaign ended `exit-1` with 86 HIR `cannot infer field type` failures across compiler and library modules. It produced no admitted Stage2 compiler, sanity receipt, or provenance receipt.
- The campaign's immutable authority was `/mnt/data/perf-feature-integrated-current`, a separate clean tree, rather than this concurrently edited shared worktree. It therefore does not establish that the shared source has the identical failure.
- The central defect is loss of imported nominal owner provenance before HIR field lowering: owner-qualified layout resolution must precede import-placeholder reuse. The old deployed `bin/simple` remains non-admissible and was not used as a fallback.
- A focused Rust lowerer regression for an imported `Attribute.args: [Expr]` completed without a reported failure (diagnostic seed evidence only). A collision-safe completion still requires preserving canonical owners by receiver `TypeId`; the existing bare-name metadata is order-dependent when two imported layouts share a name.

## 2026-08-13 canonical Viz direct-frame numeric admission

- The aggregate walker now validates finite frame metadata, rectangles, transforms, quad numeric fields, and shared-quad-state opacity/color ranges in addition to SQS index bounds. Direct entity-frame callers therefore cannot inject NaN, infinity, or an invalid blend alpha into renderer-facing composition.
- The typed surface composition spec adds NaN-geometry and opacity-range rejection cases. It remains source-only until an admitted self-host compiler is available.

## 2026-08-13 Viz numeric admission review

- Highest-tier source review PASS: the aggregate walker uses the established self-hosted finite-coordinate predicate (`value == value` plus a bounded envelope), rejects empty/inverted render geometry while permitting finite empty sentinel rectangles, and validates numeric state before copying renderer-facing passes. Executable Simple evidence remains HOLD because no admitted compiler exists.

## 2026-08-13 Linux personality matrix boundedness

- The fixed v1 14-capability matrix now rejects overflow additions without changing its count or stored rows. Its declared capability list was aligned with the persisted 14-slot schema (no unrepresented devfs row). A source unit case covers the fifteenth insertion; runtime evidence remains HOLD pending an admitted compiler.

## 2026-08-13 SimpleOS calendar conversion safety

- Calendar conversion now rejects null/out-of-range `gmtime` input, normalizes `mktime` month/day/time fields within the bounded 1970–9999 profile, and prevents `strftime` temporary-buffer overflow from malformed years. `clock_gettime` also initializes its syscall-result scratch buffer defensively.
- The focused calendar C harness passed under AddressSanitizer and UBSan with SimpleOS headers. Reentrant wrapper null guards are source-aligned; their dedicated harness remains future coverage.

## 2026-08-13 SimpleOS aligned-allocation ownership boundary

- `posix_memalign` no longer returns anonymous mmap or interior over-allocation pointers that `free` cannot own. The present dlmalloc contract supports only its proven 16-byte payload alignment; larger/page-aligned requests fail closed with `ENOMEM`.
- Strict C evidence passed for a freeable aligned result and for invalid, over-aligned, and page-aligned failure semantics. A future allocator-owned aligned-block representation is required before wider alignment is advertised.

## 2026-08-13 SimpleOS C++ aligned-new honesty

- C++17 scalar and array aligned-new now share the allocator's proved 16-byte alignment boundary. Unsupported `align_val_t` values abort in the no-exceptions ABI rather than returning under-aligned storage; nothrow new also honors the zero-size allocation invariant.
- The matching sized/unsized scalar/array aligned-delete and aligned-nothrow ABI symbols now preserve owned `free` lifecycle semantics. The strict C ABI harness passed valid scalar/array allocation, delete forms, nothrow failure, and subprocess termination for an unsupported 64-byte throwing request. A real SimpleOS C++ sysroot smoke remains additional target evidence.
- A host C++17 `alignas(64)` compile confirmed the expected throwing aligned-new/sized-delete mangled symbols. That checks ABI spellings only; it is not target execution evidence.

## 2026-08-13 SimpleOS epoll_pwait mask honesty

- The poll-backed epoll shim no longer discards a requested `epoll_pwait` signal mask. A non-null mask now returns `ENOSYS`; only the `NULL` mask path delegates to ordinary epoll wait behavior.
- The focused target-header C harness passed both rejection and preserved `NULL` wait semantics. Full atomic mask/wait remains a kernel signal-owner prerequisite.

## 2026-08-13 SimpleOS pthread synchronization honesty

- Mutex/rwlock operations no longer return false-success no-ops. Until a kernel-owned atomic lock/futex and wait handoff exists, their usable operations return `ENOSYS` and required null arguments return `EINVAL` without mutating caller storage.
- The strict target-header C harness passed mutex/rwlock error paths and preservation checks. This deliberately does not claim pthread concurrency support.
