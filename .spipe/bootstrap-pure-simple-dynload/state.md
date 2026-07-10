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
- implement: Stage 4 `-c` smoke no longer depends on shelling out for current-exe discovery, file-exists checks, sibling seed lookup, or snippet staging; wrapper Stage 4/5 native-build now exports `SIMPLE_STUB_MISSING_RT=1` to match focused core-C link evidence.
- verify: Focused Stage 4 native-build still links with zero unresolved `rt_*`; the smoke now reaches `interpret_file` and fails with an empty parse diagnostic instead of hanging or failing temp-file staging.
- implement: Fixed bootstrap weak-stub classification so hosted libc process/stdio symbols (`popen`, `pclose`, `fgets`) are left for the platform linker instead of being weak-stubbed; the previous stubs made Stage 4 seed delegation return no output even when `SIMPLE_BOOTSTRAP_DRIVER` pointed at the Rust seed.
- verify: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler --lib test_bootstrap_stub_mode_defers_libc_process_symbols_to_linker` passed.
- verify-warn: Package-level `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler test_bootstrap_stub_mode_defers_libc_process_symbols_to_linker` is blocked by an unrelated existing integration-test compile error in `compiler/tests/smf_template_integration_tests.rs` (`ClassDef` initializer missing `is_value_type`).
- verify: `cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler` passed with existing warnings.
- verify: `sh -n scripts/bootstrap/bootstrap-from-scratch.sh` passed; `sh scripts/bootstrap/bootstrap-from-scratch.sh --help` still documents `--full-bootstrap` and `--mode dynload|one-binary`.
- verify: `sh scripts/setup/install-spipe-dev-command.shs --check`, `sh scripts/audit/direct-env-runtime-guard.shs --working`, and `sh scripts/audit/direct-env-runtime-guard.shs --staged` passed; `find doc/06_spec -name '*_spec.spl'` produced no entries.
- implement: Reverted macOS native-link `-no_uuid` suppression in the Pure Simple linker wrapper. The 2026-07-10 full-bootstrap run produced a Stage 2 Mach-O that current macOS dyld refused before Stage 3 with `missing LC_UUID load command`; launchability takes precedence over byte-stable LC_UUID suppression for deployed bootstrap executables.
- verify-warn: Full bootstrap rebuilt the Rust seed/runtime and reached Stage 3, but Stage 3 failed immediately on the missing LC_UUID before this fix. Stage 4 fallback to the Rust seed then became CPU-bound with no new object output for about 17 minutes and was interrupted; sample captured at `build/bootstrap/logs/aarch64-apple-darwin/stage4-worker.sample.txt`.
- verify-warn: Fresh isolated `bootstrap_main.spl` native-build after the LC_UUID fix now fails earlier in Cranelift verification for `app.cli.bootstrap_main:bootstrap_output_from_args`; this is a separate fresh-cache compiler blocker and was not retried to avoid a runaway loop.
- verify: `bin/simple check src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` passed after the LC_UUID fix.
