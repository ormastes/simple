# smux configured/literal specs: native children never provisioned (2026-11-14)

**Status:** OPEN. Specs left RED (not weakened, not skipped).

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
