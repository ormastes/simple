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
