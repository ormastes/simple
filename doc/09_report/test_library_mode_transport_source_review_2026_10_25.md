# Test library-mode transport source review — 2026-10-25

Status: **WARN / NOT_RUN** — source review complete; no open P0/P1/P2 findings in this scoped delta. This independent review concerns the canonical test runner's explicit semantic library-profile transport. It is not a compiler, runtime, native fixture, or release qualification. Baseline: `0c74b566af53b95a548f24bd9c34c7fa34771df6`. Final review checkout HEAD: `a4d9fe7688e252dbbf2b5f3a62c231e69266119b` (the intervening application migration did not alter these runner owners). The separately reviewed application import migration is outside this delta.

## Scope and source findings

The frozen eleven-file manifest is `build/review/test-library-mode-transport-freeze-v2.sdn` (initial freeze retained separately). No compiler, test runner, helper binary, or native fixture was executed during this review. Source inspection and hashing are not executed test cases.

**P2 — profile-unbound resume checkpoint (closed by source correction).** The initial candidate accepted `--library-mode` with `--resume`. The canonical main loaded the global checkpoint before dispatch, skipped completed paths, and imported its totals without matching the selected profile. An entirely completed selection could return checkpoint totals without compiling the requested profile. Disabling the ordinary result cache did not disable this branch. The corrected candidate uses `native_test_library_resume_error` in argv validation and again on effective `updated_options` after CI/bootstrap defaults, before discovery or any checkpoint access. The checkpoint branch consults that same effective request. A selected profile with resume now returns an attributable failure before importing totals or skipping files; empty-profile resume remains accepted. Two additional authored controls cover both argument orders/spellings and a later effective-options merge. These controls were inspected, not executed. The manual also requires a retained-checkpoint native negative test proving no read/delete or carried totals.

No other concrete P0/P1/P2 issue was found in the inspected transport delta.

## Reviewed behavior

- `TestOptions.library_mode` defaults to empty. Validation reuses `compiler.common.library_mode_policy_v1`; parsing consumes both flag spellings and rejects invalid, missing, and duplicate selections. The host runner's family does not select the child profile.
- Explicit native AOT carries the exact token through `build_child_args`, its async worker caller, the reparsed sequential child, and `native_test_compile_args_with_threads`. Direct sequential execution uses the same options. The discovered QEMU `.spl` helper also reaches this child builder. The existing fork flag does not introduce another execution dispatch in canonical main.
- Explicit backend parsing disables legacy result-cache and session-daemon use. Current sequential and parallel result-cache branches are disabled. Native compilation creates its owned artifact and cache rather than consuming a prior result verdict. Existing compile, producer-identity, terminal-process, artifact, and cleanup gates remain in place.
- The selected mode joins the ordered-source identity only when nonempty. The executable name, its private cache path, and metrics thereby distinguish otherwise identical explicit profiles. Empty selection preserves the old identity and executable-path construction. Compiler-owned configured resolution and closure hashing remain downstream responsibilities.
- Contradictory execution modes, interpreter/SMF/auto routes, safe/container/composite requests, and requested or configuration-enabled doctest lanes are rejected rather than silently dropping the profile. Missing implementations for another profile remain errors; no copied family facade or physical-family source-root pin is introduced.
- The framework wrapper and its real assertion counters are not replaced by this change. The transport tests inspect actual parser/builder/identity helpers, but do not establish that native compilation or framework execution works.

## Evidence still required

All sixteen authored transport cases (zero executed) and the real framework fixtures remain **NOT_RUN**. Required future evidence includes the admitted Phase 3 producer and runtime identities; actual configured NoGC native resolution; positive three-case execution; deliberate three-case failure continuation with the expected nonzero verdict; parallel-child forwarding; profile-isolated artifacts; unsupported-route diagnostics; and terminal cleanup receipts. No source-only result substitutes for these checks.

## Final source pins

All eleven file hashes were independently matched to the v2 freeze manifest during focused review cycle 2. Seven changed from v1; the other four retain the already reviewed bytes. No compiler or test process was launched.

| Path | SHA-256 |
|---|---|
| `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl` | `8f758fa71e5d778d36bb1110ad778cabf81fa92892b4849cf302f228b278c370` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` | `b19816997cd9c29084f5389dbd9e03a3bac1383b865b5bb9c1971575665e7f0e` |
| `src/lib/nogc_sync_mut/test_runner/native_compile_contract.spl` | `633941b47620af71155a41f5bc45699479e2e46a7cb4941648e207d4e984aabd` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` | `96b80af17769a1c0d2b074fee26bef4646988e7a7d4f3cb7ae47211a14191007` |
| `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` | `255c5b3beb75246e5263df5e22f808ff24cb2f96c842fff3ac8a239cdd155c42` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_metrics.spl` | `ff32740a7ace9d54e951806493b3470a61e258607163cdeaf0bd1016bebbf6d4` |
| `src/app/test_runner_new/test_runner_main.spl` | `410271e6b34d4217489948245079446c4ec66077a11e24db0311e64fed5bc82b` |
| `src/app/cli/tool_help.spl` | `a4ac7f21cc8440cebb62c5302de0dd387bc1339dc4beafc3589acac3861b44f4` |
| `test/01_unit/lib/test_runner/library_mode_transport_spec.spl` | `f799a0e74e611377a0fb952bf2e8eaae4ed46b63af71f27619520a0897c18bd3` |
| `doc/06_spec/01_unit/lib/test_runner/library_mode_transport_spec.md` | `bf295caac2e6fe58f7771c28f57a4645d1daef7683dfdb041428a891a8b1ec14` |
| `doc/05_design/native_sspec_framework_wrapper.md` | `679809a5053ec96039ae59c724775feddf478873e167e33508881d58d31229c4` |
