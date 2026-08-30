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

## Findings 2026-08-23

- Mach-O weak definitions misread as STRONG (stage-2 blocker, fixed): stage2
  native-build exit 1 with "Stage4 runtime capsule defines owner-provided
  runtime symbols STRONGLY ... _rt_heap_live_bytes, _rt_heap_peak_bytes". Apple
  llvm-nm prints weak *definitions* as `T` in POSIX `-g -p` output; the weakness
  only appears in the `-m` flag field as `weak external`. The seed's
  `archive_weak_global_symbols`
  (src/compiler_rust/compiler/src/pipeline/native_project/tools.rs) and
  `read_global_symbol_types`
  (src/compiler_rust/compiler/src/pipeline/native_project/linker.rs) accepted
  only GNU/ELF `W`/`V`, so every `__attribute__((weak))` C fallback looked
  STRONG and the stage-4 runtime capsule gate refused the link. Fix: pass `-m`
  to nm on macOS hosts and normalize `weak external`/`weak reference` lines to
  weak in both parsers. Verify: `nm -m` shows `weak external _f` where
  `nm -g -p` shows `T _f` for the same weak definition.
- Per-file 300s timeout is a hard default, not tunable: `file_timeout: 300` in
  src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:537 (config
  builder `.timeout(secs)`); no env var or CLI flag override exists. The
  `--timeout` flag of `simple native-build` is the *worker subprocess* timeout
  (default 7200), owned by src/app/cli/native_build_main.spl — a different knob.
  On a saturated 10-core/24GB host (`--jobs=full`, ~950% CPU) big files (e.g.
  src/compiler/10.frontend/core/__init__.spl) can exceed 300s; retry with
  `--jobs=half` — the native cache resumes and only failed/uncached files
  recompile. Same file passing with fewer jobs = contention, not a hang.
- Fresh-seed requirement for current source: current `src/` uses `unsafe(...)`;
  seeds/deployed binaries older than ~2026-08-19 fail with `error[E1002]:
  function 'unsafe' not found`. A `--full-bootstrap` rebuild of the Rust seed
  from current `src/compiler_rust` is the only way to compile current source;
  there is no working prebuilt compiler for a red/green loop on this host right
  now.

- handoff (2026-08-25 ~06:20, session d495243d — READ THIS FIRST, nothing below needs re-deriving):
  - **Timeout fix ALREADY LANDED — do not redo.** PR #24, branch `caret-devtools-2026-08-25`, commit `991c88e543c`. Origin's `scripts/bootstrap/bootstrap-from-scratch.sh` has TWO timeout blocks (3740-3743 and 5118-5121, the second inside the folded `resume-stage3` function) plus `scripts/check/lib/bootstrap-stage3/sanity.shs:369-372`; all are now `${VAR:-N}` with defaults unchanged (5/60/5/1). Guard: `scripts/check/check-bootstrap-timeout-env-overridable.shs` (`PASS — 13 assertion(s) across 3 site(s)` on branch content; fatal `--selftest`, 5 fixtures; sabotage FAIL / restore PASS verified). Bug record: `doc/08_tracking/bug/bootstrap_build_timeout_not_env_overridable_2026-08-25.md`. NOTE: the shared tree `/mnt/data/worktrees/simple-main` carries another session's UN-FOLDED WIP copy of `bootstrap-from-scratch.sh` (-3847 lines vs origin) and an untracked `scripts/bootstrap/resume-stage3-from-admitted.sh` — **never `git checkout` or commit those paths in the shared tree**, it would destroy that WIP.
  - **Private worktree:** `/mnt/data/tmp/claude-1000/s4-chain`, `git worktree add --detach` at origin tip **a3bda7bfc2175239aa0ca7a53fbe95cfade825c0** (origin moved past e8db788629b). Timeout fix applied locally there via sed; warm cache seeded before first build (`build/native_cache`, 183 `.o` copied from the shared tree). Tree is otherwise clean.
  - **Exact resume command** (detached; never foreground, the 10-min harness cap kills it):
    `nohup setsid sh /mnt/data/tmp/claude-1000/s4-stage2.sh > /mnt/data/tmp/claude-1000/s4-stage2.log 2>&1 < /dev/null &`
    where that script does: `cd /mnt/data/tmp/claude-1000/s4-chain`; `export COMPILER_BUILD_TIMEOUT_SECONDS=600 COMPILER_PROBE_TIMEOUT_SECONDS=60 COMPILER_EXEC_TIMEOUT_SECONDS=60 SIMPLE_CACHE_SCOPE=s4chain SIMPLE_NATIVE_INCREMENTAL=1 SIMPLE_TIMEOUT_SECONDS=0`; then
    `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --output=build/bootstrap/s4chain --mode=dynload --backend=cranelift --jobs=4`.
    Logs: main `/mnt/data/tmp/claude-1000/s4-stage2.log`; per-stage `build/bootstrap/s4chain/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`; progress telemetry `build/bootstrap/s4chain/bootstrap-progress.log` (30s samples, `phase=`/`stall_streak=`). Keep `--jobs=4` — earlyoom kills jobs=8 on this box.
  - **How far it got:** Rust seed rebuild OK -> `rust-native-all-build` -> `rust-runtime-nolto-build` -> **Stage 2 BUILT CLEAN**: `Build complete: 757 compiled, 0 cached, 0 failed`, linked 28405 KB via clang++, `Time: 883.7s compile + 91.7s link = 975.5s total`. Then **REJECTED at sanity**: `error: sanity FAIL - frontend smoke exited 2 (bootstrap-mode pass: 0)` / `bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.0-RC unsupported_status=1 frontend_status=2 candidate_unchanged=true`. Candidate preserved at `build/bootstrap/s4chain/stage2/x86_64-unknown-linux-gnu/simple.rejected`, sha256 `3879386750f07d1155b7befa5f89da294fac8618f714de3ef857349e701f993a`. Wrapper exit 2. Stage 3 and Stage 4 were never reached; **no Stage 4 CLI exists**, so the 5 llm_caret specs stay blocked on exactly the condition already recorded above.
  - **This is a DIFFERENT failure from the 2026-08-25 05:45 budget miss.** That one was `frontend smoke exited 1` under a clamped 60s budget; this run honoured `COMPILER_BUILD_TIMEOUT_SECONDS=600` and still failed with **`exited 2`** — and 2 is not `timeout(1)`'s 124/137, so it is a genuine smoke error, not a budget miss. Next session's FIRST move: replay `candidate_frontend_smoke` by hand against `simple.rejected` (argv in `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:36-85`: `native-build --backend cranelift --runtime-bundle core-c-bootstrap --entry-closure --entry scripts/check/cert/redeploy_gate/fixtures/p2_add.spl --mode one-binary`) and CAPTURE ITS STDERR — the wrapper discards it, which is why the diagnosis helper still says `UNDIAGNOSABLE: the stage failed with no error message of any kind` (531-byte log, no diagnostic line). Fixing that stderr-swallowing is the open follow-up already filed in the bug record above; it is now the single biggest blocker to progress on this lane.
  - **Also note:** `--mode=dynload` is a no-op at Stage 2 — the log says `E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED: --mode 'dynload' is not implemented by the Rust seed and is SKIPPED; emitting a single native artifact (--mode one-binary) instead`. And there was **no `[native-incremental] N reused / M rebuilt` receipt at all** (0 occurrences): the seeded warm cache was written under a different `SIMPLE_CACHE_SCOPE`, and entries are partitioned by a scope-derived DIRECTORY, so `0 cached` is the expected scope-partition consequence, not a broken cache. To actually reuse it, seed the cache INTO the `s4chain` scope subdirectory or reuse the scope that produced it.
  - **Planner-receipt contract for Stage 3/4 (discovered; do NOT forge).** `--stop-after-stage2` is the ONLY receipt-free lane ("trust-root exception"). Stage 3 (`--resume-stage3-from-admitted=<output>` / `--stop-after-stage3`) and Stage 4 (`--resume-stage4-from-admitted=<output>`, which additionally REQUIRES `--deploy`) verify a `simple-bootstrap-planner-admission-v2` receipt or `exit 64`. The receipt binds 28 keys (`scripts/check/lib/bootstrap-planner-admission-bound.shs:72+`), including `cache_scope_key == sha256("<runtime_snapshot_sha256>:<planner_source_closure_snapshot_sha256>")`, an authorization-text cross-check, and every `*_path` re-hashed against its `*_sha256` — it is unforgeable in practice and forging it would be defeating an authorization gate. Legitimate producer (from the wrapper's own error text at `bootstrap-from-scratch.sh` ~4404):
    `simple run src/app/build/bootstrap_receipt_main.spl --bootstrap-reason=<typed-reason> --bootstrap-target=//bootstrap:stage3 --bootstrap-receipt=<path> --parent-compiler-sha256=<hex64> --runtime-snapshot-sha256=<hex64> --planner-source-closure-sha256=<hex64> --planner-sha256=<hex64>`
    (the wrapper's internal admission runs the admitted planner under `env -i LC_ALL=C LANG=C TZ=UTC PATH=/usr/bin:/bin SOURCE_DATE_EPOCH=0 SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH=<runtime>` — so **no exported timeout reaches the planner**; a receipt-production timeout would be a NEW unconditional-budget site, not one the landed fix covers). Reason codes are a CLOSED list (`bootstrap_planner_v2_reason_allowed`); the truthful ones here are `//bootstrap:stage3:seed-cannot-parse-required-language-feature` (grounded in the open seed parser regression) and `//bootstrap:stage4:self-host-convergence-check`. If any bound key cannot be filled truthfully, STOP and report which one — do not improvise a value.
  - **Deploy safety:** the wrapper's deploy step writes repo-root-RELATIVE `bin/release/<platform>` (`bootstrap-from-scratch.sh:1399`) and refuses a symlinked `bin`/`bin/release`/deploy dir (`:1403`), so `--deploy` inside the private worktree cannot touch the shared tree. A Stage 4 must still be reported (path + sha256 + `--version`) to the orchestrator rather than deployed to `/mnt/data/worktrees/simple-main` — a parser-regression deploy decision is pending there.
  - **Spec helpers already written** (reusable, no re-derivation): `/mnt/data/tmp/claude-1000/s4-helpers/write-provenance.sh <worktree> <caret-artifact>` emits all 8 required `caret.provenance` keys computed from the tree and REFUSES to write if `--version` matches `bootstrap|seed` or `git status --porcelain` is non-empty; `/mnt/data/tmp/claude-1000/s4-helpers/run-spec.sh <worktree> <label> <cmd...>` runs one spec bracketed with `readlink -f`/`stat`/`sha256sum` before and after, ANSI-strips, and greps the `Results:` line (never `tail -1`).
