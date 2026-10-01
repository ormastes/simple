# Plan acceptance shard project context and database contention

Date: 2026-09-22. Base: 6dbcbaa5c38.

## Defect and correction

The push sweep copied tagged specs into OS temporary directories. Those paths
have no repository ancestor, so project import resolution lost `src/`.
Preserved integration logs show E1034 for `os.qemu_systest_contract`,
`app.wm_compare.graphical_backend_equality`, `compiler.driver.driver_codegen`,
and `app.spipe.kb`. Shards also entered shared test database/report persistence.

The gate now allocates its unique work directory under `$ROOT/build`, keeping
the real source closure reachable through project ancestor detection. Specs,
classifiers, E1034 rejection, and per-job temporary/storage isolation are unchanged.
Directory sweep invocations add `--no-db`: runner argument parsing sets only
`no_db`; result classification and verdict emission precede the guarded database
update in `test_runner_main.spl`. Exit-code calculation remains active.

## Evidence

- Shell syntax and `git diff --check`: PASS.
- Gate selftest: 17 assertions PASS; 13.76 s real, 1.14 s user, 2.15 s system;
  maximum resident set size 3,080,192 bytes (`/usr/bin/time -l`). This profiles
  fixture orchestration, not the full source suite.
- Mutation restoring OS-temp staging: new fixture FAIL with E1034 and gate ERROR.
- Mutation removing `--no-db`: new fixture FAIL with missing neutralisation markers.
- SoSIX capsule gate: PASS, 18 file/gate checks, zero violations; direct-rt count
  6222 against ceiling 6294. Shell-only change adds no host ABI or runtime facade.
- Independent Astra read-only review: approved, no blocking defects.

## Validation limit

No duplicate full sweep was launched. A bounded source import probe using
`/Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple` discovered that
this artifact identifies itself as a Rust bootstrap seed, despite its release
path; parsing failed in `src/os/simpleos_config_matrix.spl`. It is not accepted
as self-hosted runtime validation. The mock fixtures protect gate wiring, not
real import execution. Integration must supply actual full-sweep evidence with
its admitted runtime; no release readiness PASS is claimed here.
