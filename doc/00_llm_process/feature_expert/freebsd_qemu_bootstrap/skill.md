# Feature Expert — FreeBSD QEMU Bootstrap Lane

## Role

Own process knowledge for bootstrapping Simple natively inside a FreeBSD
x86_64 guest under QEMU. The goal is a canonical
`FreeBSD x86_64 QEMU Stage 3 bootstrap PASS`, then a Stage 4 full CLI and the
compiler/interpreter/loader specs, all running on FreeBSD.

## Pipeline Links

- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)

## Feature Links

- Host wrapper: `scripts/check/check-freebsd-bootstrap-qemu.shs --full`
- Guest checker: `scripts/check/check-freebsd-selfhost-ci.shs`
- Contract tests: `test/01_unit/scripts/freebsd_qemu_invocation_contract_test.shs`,
  `test/01_unit/scripts/freebsd_selfhost_ci_contract_test.shs`
- CLAUDE.md § FreeBSD QEMU Bootstrap Check (env knobs)

## Load-bearing facts

- The guest is amd64. On an aarch64 host (the Grace box) it runs under TCG,
  with no KVM. Measured 2026-09-19 with `QEMU_CPUS=8 QEMU_MEM=12G
  SIMPLE_FREEBSD_SELFHOST_JOBS=6`:
  - rust-seed-build: about 1.5h
  - rust-native-all-build: about 70m
  - rust-runtime-nolto-build: about 13m

  At `JOBS=1` the seed build alone took 3.5h (2026-09-18).
- Three separate timeouts bound a run:
  - `QEMU_BOOTSTRAP_TIMEOUT` is the guest checker budget (default 8h).
  - `QEMU_FULL_TIMEOUT` is the host ssh session. It now defaults to the
    bootstrap budget, and preflight refuses a smaller value (#1121).
  - `SIMPLE_NATIVE_FILE_TIMEOUT` is the per-file native-build cap. It is 300s
    unless set, and the guest checker now defaults it to 1800s (#1122).
- On success, wrapper cleanup deletes the overlay. To keep a finished guest for
  follow-up work (Stage 4, specs), hard-link the overlay before the run ends,
  then boot the kept image again.
- Stage 4 full CLI is refused on FreeBSD by `bootstrap-from-scratch.sh`
  (`full_cli` host gate: Linux|Darwin only). The Stage 4 link is done by the
  pure-Simple Stage 3 compiler, not the Rust seed linker.

## Traps that have cost time

- The 2026-09-18 run was killed at exactly 5h (18000s) with no reason
  printed: the ssh cap was shorter than the raised bootstrap budget. The
  checker now reports its exit code and names ssh timeouts (124).
- The 2026-09-19 run stalled silently at rust-seed-build when the root
  filesystem hit 3G free. QEMU's default `werror=enospc` paused the guest, and
  with no monitor socket nothing could resume it. The wrapper now refuses to
  start with less than `QEMU_MIN_FREE_GB` (30) free and uses `werror=report`.
  On a full root disk, set `QEMU_RUNTIME_DIR=/dev/shm/<dir>`.
- The 2026-09-17 Stage 2 failure "2 file(s) failed to compile" was per-file
  timeouts (`10.frontend/core/__init__.spl`, `method_calls_literals.spl`), not
  compile errors. #1061 made Stage 2 honor `SIMPLE_NATIVE_FILE_TIMEOUT`, but
  nothing on this lane set it until #1122.
- Stale `/tmp/*verdict*` and `/tmp/ci-retry.out` files come from other
  sessions. Read the run's own log dir (`build/freebsd/bootstrap-logs/`), not
  shared `/tmp` artifacts.
- Editing the wrapper while a run is live is safe only through
  rename-replacing edits (`sed -i`, `git switch`). The running `sh` keeps the
  old inode, as `/proc/<pid>/fd` shows `(deleted)`. An in-place write would
  corrupt the rest of the run.
