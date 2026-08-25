# Feature: bootstrap-pure-simple-dynload

## Raw Request
however update doc and script, when bootstap not to rebuild rust build unless it is full bootstrap. and pure simple build config be 2 one binary and dynload modes. dynload be default to speed up rebuild. and if possible improve dependency tracing to rebuild only changed codes(becareful with aop). add agent refactor bootstrap and simple/compiler,interpereter,loader arch.

## Task Type
code-quality

## Refined Goal
Make the bootstrap contract explicit and enforceable: normal bootstrap reuses the existing Rust seed, full bootstrap is the only mode that rebuilds Rust, and pure-Simple rebuilds default to dynload with an opt-in one-binary mode plus documented dependency-invalidation constraints.

## Acceptance Criteria
- AC-1: `scripts/bootstrap/bootstrap-from-scratch.sh` treats Rust rebuilds as full-bootstrap-only and exposes a clear full bootstrap flag/help contract.
- AC-2: Pure-Simple bootstrap has two named build modes, `dynload` and `one-binary`, with `dynload` as the documented/default mode for faster rebuild iteration.
- AC-3: Dependency tracing guidance states what can safely rebuild from changed source only and what must invalidate broadly for AOP/MDSOC weaving, compiler ABI, loader, or interpreter changes.
- AC-4: Bootstrap/compiler/interpreter/loader architecture documentation records the refactor boundary and sidecar-agent review plan.
- AC-5: Focused verification covers shell syntax/help output and doc freshness without re-running a full bootstrap.

## Scope Exclusions
- No full compiler dependency-cache rewrite in this lane unless existing code already exposes a safe narrow hook.
- No release, tag, or push until verify is green and the user asks to ship this lane.

## Cooperative Review
- Sidecars:
  - Epicurus the 2nd: bootstrap script/doc behavior explorer.
  - Aquinas the 2nd: dynload/native-build/compiler/interpreter/loader surface explorer.
  - Poincare the 2nd: dependency tracing and AOP/MDSOC invalidation explorer.
- Merge owner: Codex main thread.
- Final reviewer: Codex main thread.
- Shared interface names: `SIMPLE_BOOTSTRAP_MODE`, `--mode dynload|one-binary`, `--full-bootstrap`.
- Manual step helpers: N/A, no SSpec authored in this lane.
- Setup/checker helpers: `sh -n scripts/bootstrap/bootstrap-from-scratch.sh`, `scripts/bootstrap/bootstrap-from-scratch.sh --help`, `find doc/06_spec -name '*_spec.spl' | wc -l`.
- Fail-fast placeholders: N/A, no new executable specs.
- Generated-manual review owner: N/A, no generated spec changes planned.

## Phase
verify-warn

## Log
- dev: Created state file with 5 acceptance criteria (type: code-quality).
- implement: Added `--full-bootstrap` gate, `--mode=dynload|one-binary`, Rust seed warning output, native-build mode parsing, and conservative native-cache reuse.
- implement: Updated bootstrap/tooling/compiler architecture docs, SSpec/manual docs, and dynSMF manifest count drift from six to seven entries.
- review: Sidecars completed read-only review for bootstrap behavior, dynload/loader surfaces, and dependency tracing/AOP risk; merged findings into docs.
- verify: `sh -n scripts/bootstrap/bootstrap-from-scratch.sh` passed; `sh scripts/bootstrap/bootstrap-from-scratch.sh --help` shows `--full-bootstrap` and mode help.
- verify: `bin/simple check src/app/cli/native_build_main.spl` passed.
- verify: `bin/simple test test/03_system/feature/app/native_build_smf_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 7/0.
- verify: `cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-driver` passed after fixing the existing unconditional `RefCell` import; existing runtime extern signature warnings remain.
- verify: `bin/simple spipe-docgen test/03_system/feature/app/native_build_smf_spec.spl --output doc/06_spec --no-index` generated 0 stubs; duplicate generated path was discarded in favor of the existing canonical manual path.
- blocked: `bin/simple check src/app/io/_CliCompile/compile_targets.spl` terminated twice with exit 143 during dependency loading; not re-run to avoid a runaway loop.
- deploy (2026-08-25 05:16 UTC, seed-sibling refresh, NOT self-hosted): `bin/release/x86_64-unknown-linux-gnu/simple` pre `f6521b60b67d38944016b82451ac60c522375410c60dec7178d5c06bd063bde7` (2026-08-23 04:47) -> post `706fa63677e053add9e09b8a2238dbece43019ce43cdaca5e95bc30be53689d6` (Rust seed, cargo from CLEAN worktree at origin/main `e8db788629b`, `cp -> .new && mv`). Smoke: arithmetic `5`; value-bound `unsafe(...)` probe `V=/home/ormastes` (bug `deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25.md` -> FIXED). Regression guard on the new binary, brackets stable at `706fa636…`: agent_workspace_spec 6/6, workspace_cli_system_spec 4/4, infra_tools_spec 17/17, check-llm-caret-infra-live `PASS — 2 live row(s)`. Rollback receipt: `/mnt/data/tmp/claude-1000/seed-rollback/RECEIPT.md`.
- blocked (2026-08-25): the 5 llm_caret cached/closure/phase specs still need a genuine Stage 4 (`runtime=pure-simple-self-hosted`, `--version` without `bootstrap|seed`) plus a hand-written `build/bootstrap/caret-package/caret.provenance` and a CLEAN tree (the cached checkers fail closed on a dirty tree, so they can never pass on the shared tree). Stage 3 self-host is not converging on this box: lane simple-work-20260824 `abnormality-source-stage26` failed 05:17 UTC with `10.frontend/core/__init__.spl: timeout (600s)`; earlier stage3 attempts there stall at seq=685. Own attempt: `caret-clean` (origin/main e8db788629b) `bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --output=build/bootstrap/caret-redeploy --mode=dynload --backend=cranelift --jobs=8`, SIMPLE_CACHE_SCOPE=caret-redeploy — see the Phase log below for the outcome.
- finding (2026-08-25 05:45, Stage 2 admission is load-flaky): the pinned-clean-worktree Stage 2 BUILT fine — `Build complete: 757 compiled, 0 cached, 0 failed`, 28409 KB linked — but the wrapper rejected it at sanity: `error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)` / `bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.0-RC unsupported_status=1 frontend_status=1 candidate_unchanged=true`, binary preserved as `stage2/x86_64-unknown-linux-gnu/simple.rejected`, wrapper exit 1, and the failure-diagnosis helper reported `UNDIAGNOSABLE: the stage failed with no error message of any kind`. Replaying that exact smoke by hand against `simple.rejected` (`candidate_frontend_smoke` argv from `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`: `native-build --backend cranelift --runtime-bundle core-c-bootstrap --entry-closure --entry scripts/check/cert/redeploy_gate/fixtures/p2_add.spl`) SUCCEEDS: exit 0, `Build complete: 1 compiled, 0 cached, 0 failed`, 39 KB binary, 8.5s. So the candidate is good and the rejection was a budget miss, not a product defect: `COMPILER_BUILD_TIMEOUT_SECONDS=60` is set UNCONDITIONALLY at `scripts/bootstrap/bootstrap-from-scratch.sh:1103` (the admission helper itself honours the env at `candidate_frontend_admission.shs:4`, but the wrapper overwrites it), and 60s is not survivable on a box at load ~39 with 3 concurrent agent lanes. Suggested fix (NOT applied — outside this session's scope): make line 1103 `COMPILER_BUILD_TIMEOUT_SECONDS=${COMPILER_BUILD_TIMEOUT_SECONDS:-60}` so a loaded host can raise it, and make the sanity failure path print the smoke's captured stderr instead of `UNDIAGNOSABLE`.
- verdicts (2026-08-25 05:5x, deployed binary sha `706fa636…`, brackets identical pre/post on every run): llm_caret_cli_cached `Results: 3 total, 0 passed, 3 failed` (`failure_reason=cached_caret_artifact_missing`); llm_caret_cli_hidden_cached `Results: 5 total, 0 passed, 5 failed` (same prerequisite); llm_caret_native_closure `Results: 2 total, 0 passed, 2 failed` (`failure_reason=simple_core_archive_not_supplied`, and behind it `bootstrap_or_seed_runtime_rejected` — the deployed runtime is a seed by banner); llm_caret_tui_pty `Results: 10 total, 0 passed, 10 failed`; llm_caret_messaging_phase_cli `Results: 3 total, 0 passed, 3 failed` (Stage 3 half is satisfiable — `unknown command 'caret'` is the EXPECTED negative — but no Stage 4 binary exists to set `SIMPLE_STAGE4_BINARY`). Unblock condition for all five: a genuine Stage 4 pure-Simple full CLI deployed at `bin/release/x86_64-unknown-linux-gnu/simple` whose `--version` contains neither `bootstrap` nor `seed`.
