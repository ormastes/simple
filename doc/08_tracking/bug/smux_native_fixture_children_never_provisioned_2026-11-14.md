# smux configured/literal specs: native children never provisioned (2026-11-14)

**Status:** PROVISIONED 2026-11-15. literal 3/3 GREEN; configured 2/3 (one
remaining failure is NOT provisioning — see "Remaining failure").

## Symptom (macOS, seed release100-pty-structured-20261114)
- `test/03_system/tools/smux_configured_launch_spec.spl`: `outcome=ERROR passed=1 failed=2`
- `test/03_system/tools/smux_literal_input_spec.spl`: `outcome=ERROR passed=0 failed=3`

Both read `SIMPLE_TEST_CONFIGURED_CHILD`, `SIMPLE_TEST_CONFIGURED_CWD`,
`SIMPLE_TEST_LITERAL_CHILD`, `SMUX_CONFIGURED_REMOVE`, `SMUX_CONFIGURED_KEEP`
and fail closed when absent (spec lines 122-126, 118-119).

## Root cause
Nothing in `scripts/`, `.github/`, `test/` builds
`test/fixtures/coremux/{configured_launch,literal_input}_child.spl` or sets
those variables — grep of the env names hits only the two specs. Fixture
headers say "NOT_BUILT"; no host ever provisioned them.

## Attempted provisioning (failed)
`SIMPLE_BUILD_MEMORY_RESERVE_BYTES=4294967296 bin/simple native-build --source
test/fixtures/coremux --source src/lib --source src/app/io --entry
test/fixtures/coremux/configured_launch_child.spl` was killed by a 1800 s
timeout with no binary, still in loader/parse warnings over `src/lib`
(pure-Simple driver interpreted by the seed, cold cache). Default 12 GiB build
reserve also refuses on this 24 GB host.

## Unblock condition
A compile lane that finishes for a one-file fixture: an admitted Stage 2/3
compiler, or the seed's Rust `native_project` pipeline
(`SIMPLE_NATIVE_BUILD_RUST=1`, stable `--cache-dir`) — then a provisioning
script that builds both children, creates a `" 한글"` cwd, exports the env and
reads `SPEC FILE VERDICT`. Running the children interpreted (`bin/simple run`
shim) is an owner decision: the spec header requires a compiled fixture.

## Provisioning (2026-11-15)
`sh scripts/check/run-smux-native-fixture-specs.shs` builds both children with
the seed's Rust `native_project` pipeline (`SIMPLE_NATIVE_BUILD_RUST=1`,
`--entry-closure`, stable `--cache-dir build/smux_fixture_cache`), creates a
`"configured cwd 한글"` cwd, exports `SIMPLE_TEST_*`/`SMUX_CONFIGURED_*`, runs
both specs and reads `SPEC FILE VERDICT`. Producer must contain
`rt_stdin_read_timeout_v1` (`SMUX_FIXTURE_BUILDER=<worktree target>/release/simple`
until the next seed). Timings (macOS M4): cold 21-27 s per child (301/342
modules), warm `[native-incremental] 341 reused / 1 rebuilt`.

Named gap: the default core-c lane lacks 52 Rust-only `rt_*` symbols pulled in
by `sffi/host.spl` / io hubs (`rt_db_*`, `rt_local_unix_*_v1`,
`rt_retained_private_credential_*_v1`, `rt_profiler_*`, ...). The children never
call them, so the script sets `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` (an
accidental call SEGVs = spec FAIL, never a fake pass). `host-gpu` lane wants
`libspl_hosted_runtime-<hash>.rlib` (cargo here emits no `deps/` hashed name);
`dynamic-runtime` is Stage4-entry-only.

## Results (seed release100-ostags-20261114 runner)
- `smux_literal_input_spec.spl`: `outcome=OK passed=3 failed=0`
- `smux_configured_launch_spec.spl`: `outcome=ERROR passed=2 failed=1`

## Remaining failure (not provisioning; deterministic, 2/2 runs)
`publishes a real configured child through the public API ...`
(spec :165): after `smux_kill_session` succeeds, `sosix_pty_close(4)` on the
test-owned token keeps returning false for 200 attempts →
`CONFIGURED_API_UNCLOSED_PTY: 4`, `expected 1 to equal 0` (spec :251). Either
kill_session already closed the handle and `rt_pty_close`
(`runtime/src/value/pty.rs:1363`) is not idempotent for an owner-closed handle,
or kill_session leaks it. Unblock: decide close idempotency contract and fix
the owner; do not weaken the assertion.
