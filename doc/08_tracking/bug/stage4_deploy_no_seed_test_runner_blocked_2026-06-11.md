# stage4 deploy left no seed driver — `bin/simple test` blocked host-wide

Date: 2026-06-11
Status: reopened (2026-07-15 — current policy requires a no-seed pure-Simple test path)
Owner: stage4 deploy lane

The 2026-06-12 resolution below is retained as historical evidence. It restored
the then-supported seed-delegated workflow, but it does not satisfy the current
rule that normal checks and SSpec execution use the pure-Simple self-hosted
toolchain without `SIMPLE_BOOTSTRAP_DRIVER` or a Rust-seed fallback.

## Resolution (2026-06-12)

Rebuilt the seed with `cargo build --profile bootstrap -p simple-driver
-p simple-native-all` → `src/compiler_rust/target/bootstrap/simple`.
Two vendored-source fixes were required:

- `vendor/log/src/lib.rs`: the minimal log shim lacked the `log_enabled!`
  macro form needed by vendored regalloc2 v0.11.2 (it only had a function);
  added a no-op `log_enabled!` returning false.
- `vendor/log/.cargo-checksum.json`: updated the `src/lib.rs` sha256 so cargo
  accepts the modified vendored source.

Verified: `setsid timeout 30 bin/simple -c "print(1+1)"` → 2;
`bin/simple test` runs again via seed delegation (engine2d lane re-verified:
directx 18/18, order 4/4, cuda 7/7, rocm 7/7, acceleration 24/24, vulkan
processing 22/22, vulkan drawing 22/22). The suggested deploy-gate fix
(refuse to swap bin/simple without a working probed seed) is implemented:
`bootstrap-from-scratch.sh --deploy` now probes the `simple_seed` delegate
(installing it from a probed cargo build if absent), refuses the swap when no
working seed exists, and smoke-tests the deployed binary post-swap with
automatic restore of the previous binary on failure.

## Summary

After the stage4 self-hosted deploy (~2026-06-11 15:32, "stage4 DEPLOYED with
seed delegation"), `bin/simple` points at
`bin/release/x86_64-unknown-linux-gnu/simple` (self-hosted). Running
`bin/simple test <spec>` now fails fast with:

```
error: cannot run tests: the test runner would re-spawn this same binary (bin/simple).
  Provide a Rust seed driver via SIMPLE_BOOTSTRAP_DRIVER or keep
  src/compiler_rust/target/{bootstrap,release}/simple available.
```

The self-exec fork-bomb guard works as designed, but neither seed path
exists on this host (`src/compiler_rust/target/` has no built binaries), so
the documented remedy is not satisfiable without a full cargo build.

## Fallback attempted

`SIMPLE_BOOTSTRAP_DRIVER=bin/release/simple.bak.pre_new` runs, but that
binary fails to parse current source ("parse error: Unexpected token:
expected identifier, found Gpu") — consistent with the known self-hosted
lean-parser language-coverage gaps that had the deploy gate at matrix 6/8.

## Impact

All interpreter-mode spec verification on this host is blocked until either
the Rust seed is rebuilt (`cd src/compiler_rust && cargo build --release`)
or the deploy is rolled back to the seed binary. GPU-lane specs verified
green earlier today (backend_directx 18/18, order 4/4, acceleration 24/24,
vulkan processing/drawing, cuda/rocm processing 7/7+7/7) all ran BEFORE the
swap.

## Suggested fix

Deploy script should refuse to switch `bin/simple` to the self-hosted binary
unless a working seed driver exists at one of the two documented paths (probe
by actually running `<seed> --version`), keeping the delegation contract it
advertises.

## Reopened audit (2026-07-15)

The authoritative `simple test <spec>` call chain is still seed-owned:

1. `src/app/cli/main.spl` exports
   `src/app/cli/_CliMain/main_and_help.spl::main`.
2. Its `test` arm calls
   `src/app/io/_CliCommands/run_commands.spl::cli_run_tests`.
3. That wrapper calls `rt_cli_run_tests`.
4. `src/compiler_rust/runtime/src/value/cli_sffi.rs::rt_cli_run_tests`
   selects and spawns a seed driver and sets `SIMPLE_TEST_RUNNER_RUST=1`.

The pure-Simple orchestrator under `src/app/test_runner_new/` does not close
this gap. Its interpreter path spawns the selected binary with `run`, while
the fork path and minimal child runner ultimately call `rt_cli_run_file`; the
driver-compatible implementation in `src/compiler_rust/native_all/src/lib.rs`
explicitly executes through the Rust interpreter. The unused pure-Simple
compiler path begins at
`src/compiler/80.driver/driver_api_interpret.spl::interpret_file`, but no test
runner consumes a result-bearing BDD contract from it. The generic
`InterpreterExecutionEngine.execute_file` facade in
`src/compiler/80.driver/init.spl` is also explicitly unwired.

The smallest honest dedicated fix is therefore outside the host-GPU feature
lane: expose a result-bearing pure-Simple single-spec execution contract from
the compiler interpreter, make `run_test_file_interpreter` consume it with the
existing timeout/result safeguards, and route the CLI `test` arm to the
pure-Simple runner instead of `rt_cli_run_tests`. Acceptance needs one passing
and one deliberately failing SSpec with the candidate self-pinned, no seed
available, and no current-binary respawn loop. TODO 572 owns that work.

## Mixed-runtime argument ABI finding (2026-07-16)

The exact Stage4 profile localized the Rust closure rooted at
`rt_cli_run_tests`, including Rust `rt_array_len`/`rt_array_get`, while CLI
argv arrays are allocated by the canonical C runtime. Consequently
`simple test focused_spec.spl` reached the delegate as bare `simple test`.
Scalar `-c` arguments were unaffected. The CLI test arm now calls a scalar-only
Rust bridge which reads canonical C argv through `spl_arg_count`/`spl_get_arg`,
then uses the inherited-stdio test delegate. Parser and interpreter-registration
tests passed during refinement, but the final link remains pending after the
three-cycle cap. Acceptance is an exact candidate sentinel with
`SIMPLE_BOOTSTRAP_DRIVER=/bin/echo`; the candidate must print
`test focused_spec.spl`. The 2026-07-16 candidate rebuild SIGSEGV'd before
output, so this runtime acceptance remains pending rather than claimed.

Separately, TODO 548's shell compiler-admission replacement is now shared by
bootstrap and the QEMU wrapper. `candidate_frontend_smoke` and
`simple_binary_is_valid` live in
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`;
the smoke uses a private temporary
directory/cache/output/log,
60-second build and 5-second run bounds, EXIT cleanup, and a self-pinned
candidate (`SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and
`SIMPLE_FRONTEND_DELEGATE` all equal the candidate;
`SIMPLE_FRONTEND_DELEGATED=1`; `SIMPLE_NO_STUB_FALLBACK=1`;
`SIMPLE_EXECUTION_MODE=''`; `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`;
`SIMPLE_BOOTSTRAP=0`; and `SIMPLE_LIB=$ROOT_DIR/src`). It must native-build the checked-in
`scripts/check/cert/redeploy_gate/fixtures/p2_add.spl` with Cranelift,
core-C-bootstrap, entry closure, and one-binary mode, then run it and require
status zero plus exact stdout `5`. `_QemuRunner` now mirrors that contract with
`_candidate_frontend_smoke` and child-scoped
`_run_candidate_admission_pinned`; both the `p2_add` build and invalid-mode
probe use those admission pins, and the old whole-tree check is removed.
`build_os_with_backend` separately applies `_apply_build_env` target settings
before `_run_candidate_pinned` overlays the authoritative guest-build identity,
so the real build cannot re-enter a sibling or seed delegate after admission.
Shared CLI `_cli_is_current_exe` now resolves candidate overrides through the
existing `_cli_resolve_symlink` owner before canonical comparison, so
authoritative worker delegation also stays on symlink candidates such as
`bin/simple`. `test/01_unit/app/io/cli_argv0_resolution_spec.spl` records that
source contract; no `rt_*` alias was added.
Bootstrap retains its focused `check src/app/cli/bootstrap_main.spl`, but the
whole-tree check is no longer part of admission. The wrapper self-test and
shared-shell syntax check pass, but runner source parity is not current-source
compiler, QEMU, or GPU execution evidence. All five split `_QemuRunner` modules
now use shared I/O/process/time owners; TODO 573 retains only native child-env,
unique-temp, and cross-platform timeout process ownership. TODO 574 retains
monotonic safety.

The former `check test/05_perf/io_parity/startup_simple.spl` probe is not valid
candidate evidence. `src/app/cli/check.spl::run_check` unconditionally runs the
whole-tree repository-hygiene tail, so unrelated tracked-policy failures can
reject a correct frontend. Its Git subguards are also not authoritative in a
jj-only workspace containing `.jj` but no `.git`.

## Runtime verification (2026-07-17)

`bin/simple test r3p09_tiny_spec.spl` (env `-u SIMPLE_BOOTSTRAP`) exit 1, failed with `error: semantic: unknown extern function: rt_cli_arg_count`. This extern is declared in current `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:635` — deployed seed binary is skewed vs. current source on some externs (also affects `rt_vulkan_create_offscreen_render_pass`). Net effect matches doc's claim (`bin/simple test <spec>` unreliable on this host) though specific error differs. Broader note: deployed `bin/release/x86_64-unknown-linux-gnu/simple` lacks `rt_cli_arg_count` and `rt_vulkan_create_offscreen_render_pass` present in current `src/compiler_rust` — pending in-flight seed redeploy.
