# Lane: 1.0.0 beta release (ex-codex 019fb160)
Goal: next 1.0.0 beta (beta2 if version unchanged): local release process, fix memory/perf bugs, full bootstrap for all platforms (except mac), GH Actions release must actually succeed.
Status: development/documentation lane complete in draft PR 21; strict bootstrap,
final verification, tag, and publication remain open under TODO 652. No beta
publication is permitted from the partial evidence below.

Latest fresh rebuild: `scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload --output=build/bootstrap/release_beta_verify --no-mcp --jobs=min`
- Stage 2: PASS (`build/bootstrap/release_beta_verify/logs/x86_64-unknown-linux-gnu/stage2-native-build.log` ends with `Build complete: 728 compiled, 0 cached, 0 failed`; binary at `build/bootstrap/release_beta_verify/stage2/x86_64-unknown-linux-gnu/simple`).
- Stage 3: FAIL (`stage3` strictly fails with strict bootstrap gate), first errors are unresolved type/name errors in `src/compiler/types/type_infer/inference_effects.spl` (`Effect`, `Span`, `DimExpr`, etc.) and compiler/runtime modules (`MirFieldDef`, `SymbolId`, `rt_file_rename`, ...).
- Repro of old stage2 parser fail is no longer present after source fix: cached pre-fix stage2 failed on `true_target.id`, while fresh stage2 now compiles `/tmp/repro_beta.spl`.

See:
- `doc/08_tracking/bug/parser_true_false_prefix_call_arg_2026-08-01.md`
- `src/compiler/10.frontend/core/parser_expr.spl` (`parse_call_arg_raw` now guards true/false prefixed call arg identifiers)
- `doc/03_plan/sys_test/release_workflow_checkers.md`
Latest main-WC strict evidence (2026-08-01): Rust authority, atomic seed install, Stage 2 native build, and Stage 2 sanity PASS. Stage 3 was stopped after 15m13s at 9.7 GiB RSS with 100% CPU, no phase output, no object files, and no candidate.

Bounded diagnostic: an isolated one-thread trace probe completed entry-closure discovery for 1,758 modules, entered phase 2, parsed `src/app/cli/main.spl`, then died with signal 11 while starting `src/lib/nogc_async_mut/cli/log_modes.spl` (exit 139; 173 MiB max RSS). Evidence is retained at `build/mini_builds/release-beta-stage3-probe/probe.log`.

Next: diagnose/fix the pure-Simple phase-2 trace SIGSEGV and the profiler-only memory runaway without repeating the full build. Then perform exactly one fresh strict Stage 3 attempt; only after it passes may Stage 4, docgen, verification, and the GitHub release workflow proceed.

2026-08-01 focused repair: streaming-only differential proved the second-module SIGSEGV came from parser-global backing arrays first allocated inside a transient reclamation scope. `driver_prepare_transient_parse_scope()` now initializes reusable type/parser/AST arenas before phase-2 and phase-3 transient tracking; the streaming ownership contract asserts this ordering.

Confirmation status: attempt 1 stopped before Stage 2 because concurrent edits temporarily left Rust `lower_if` caller/signature inconsistent. Attempt 2 passed Rust compilation but failed closed while another session rebuilt the shared Rust bootstrap target during private runtime admission (`Rust runtime authority changed during private admission`). Two external Cargo owners remain active. Wait for them to exit, confirm source/runtime hashes are stable, then use the third and final verify/fix-cycle attempt. Do not run another build concurrently.

Blocked audit: this shared-authority condition persisted for three consecutive goal continuations. The foreign Stage-3 process is still CPU-bound at roughly 6.3 GiB RSS, the shared-target Cargo owner remains live, and a further external bootstrap was launched. Resume only after these owners exit; then confirm `core.bare=false` and stable source/runtime hashes before the single reserved final attempt.

2026-08-01 continuation:
- Root cause narrowed to cyclic/transitive facade-glob expansion. Required names such as `Effect`, `Span`, `SymbolId`, and `MirFieldDef` are reached through facade globs; the former pure-facade gate omitted names from mixed modules, while simply removing it caused exponential revisits and multi-GiB RSS growth.
- Added a shallowest-depth, per-root glob expansion memo in `hir_lowering/types.spl` and `_Items/module_lowering.spl`, and enabled nested glob traversal for mixed facade modules. This preserves the depth-cap reachable set while breaking cycles.
- Isolated strict native-build evidence: baseline and memoized candidates both built `728 compiled, 0 failed`; memoized compile time was 191.1s versus 253.9s baseline. `release_checker_contract_test.shs` PASS.
- Do not rerun those checks this session. Await the already-running isolated true stage2→stage3 probe, then rebuild stage2 once from the main working copy so the memo is embedded and run stage3 once. If green, proceed to the remaining release workflow checks.

2026-08-01 B/B continuation:
- The selected scope is the complete non-macOS beta with bounded-resource evidence. Final requirements, architecture/detail design, SPipe scenario/manual, and agent/system-test plans now exist under the canonical `doc/01`–`doc/06` and `test/03_system` trees.
- Release readiness now has fail-closed bootstrap/tool/platform/verification/GitHub receipt validation. Platform evidence is derived from seven downloaded executable archives with embedded revision/version/role manifests; the remote receipt is derived from a successful exact-revision GitHub run and published prerelease tag.
- The release workflow no longer permits source-only substitution for selected rows, packages the real Linux runtime rather than its repository-only wrapper, makes required installers/full package/SimpleOS/whole tests prerequisites of publication, and marks the beta release as a prerelease.
- Focused readiness, checker, platform-evidence, workflow YAML, and shell syntax contracts pass. The broader portability audit currently stops on the pre-existing missing retired-Windows-workflow restoration trigger in `rust-bootstrap-multiplatform.yml`; that unrelated workflow contract remains outside this lane.
- A shared diagnostic Stage 3 run is still active. It has crossed the 254-second release ceiling while emitting unbuffered HIR trace output, so it can prove only functional convergence, never performance acceptance. A clean isolated strict run without diagnostic tracing remains required before Stage 4 qualification and release verification.

2026-08-01 strict-run cap:
- The traced Stage 3 ended without a binary or terminal success marker after roughly 13 minutes and more than 9 GiB RSS; it is rejected evidence.
- Clean canonical cycle 1 stopped before Stage 2 on `ETXTBSY` while unrelated processes executed the seed. Seed installation is now atomic copy-plus-rename.
- Cycles 2 and 3 stopped before Stage 2 because concurrent clone work changed the shared main repository's `.git/config` to `core.bare=true` during Cargo fingerprinting. The main working copy was restored to `core.bare=false`; the clone processes subsequently ended.
- The mandatory three-cycle cap is exhausted. Do not retry this bootstrap in the same goal turn. The next continuation may make one fresh audit only after confirming `git rev-parse --is-bare-repository` remains `false` and no lane is mutating repository-local Git config.

2026-08-01 publication handoff:
- The implementation/documentation lane is complete and may be published as a draft PR.
- Strict bootstrap qualification and final `/verify` are explicitly postponed in `doc/08_tracking/todo/release_beta_bootstrap_verify_postponed_2026-08-01.md`; postponement is not PASS evidence.
- Stage 2/3 CLI evidence may be used for bounded diagnostics only. It cannot qualify the release, generate the final Stage-4 manual, create a tag, or publish artifacts.

2026-08-01 final development-lane handoff:
- Draft PR 21 is mergeable at `847e879c2e7`; the Windows-invalid duplicate paths are removed and Windows checkout succeeds.
- Focused release checker/platform contracts and the guard-wiring registry pass. Red PR checks inspected during handoff are current-main baseline failures outside the release-beta delta; they are not release qualification evidence in either direction.
- The thread goal was closed only after the user explicitly scoped completion to the development lane and required all remaining qualification work to stay in the TODO database.
- TODO 652 is the authoritative resume boundary: exact source-matched Stage 2→3→4 with stub fallback disabled and timing/RSS receipts, exact Stage-4 SPipe/manual generation, `/verify STATUS: PASS`, then tag, prerelease, artifacts, and final GitHub attestation.
