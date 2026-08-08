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
