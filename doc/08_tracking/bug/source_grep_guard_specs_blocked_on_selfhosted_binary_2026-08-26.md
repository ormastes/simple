# Source-grep guard specs un-modernizable until a self-hosted binary is deployed

- Date: 2026-08-26
- Found via: sspec modernization residual wave (batch ba, ~56 specs scoring 49 /
  SSDOC-ORA-002).

## Class

These specs pin `src/app/**` implementation shapes via source-grep assertions
(`expect(source.contains(...))`). Behavioral oracles are unreachable on the
current deployment: `bin/simple` is the **Rust seed** (banner verified), and
this worktree has no `bootstrap/` stage binaries (tracked stage artifacts
absent; per the 2026-08-18 guard record they SEGV anyway). The seed's `lint`
emits findings only as unscoped startup noise over compiler sources — never a
`-->`-scoped diagnostic for an arbitrary fixture — so a scoped behavioral
oracle against the pure-Simple CLI paths cannot be built.

Faking behavioral assertions against the seed would test different code than
the specs pin and violate the never-weaken rule, so they are left as-is.

## Unblock

Deploy a working self-hosted `bin/simple` (`scripts/setup/setup.shs && bin/simple
build bootstrap`), then rewrite each source-grep scenario to invoke the real
CLI (`rt_process_run`) and assert observable output.

## Representative members

- `test/01_unit/app/auto_coverage_*_spec.spl` (12)
- `test/01_unit/app/branch_coverage_*_spec.spl` (~19)
- `test/01_unit/app/test_runner/**` guard specs
- `doc/06_spec/x25519mlkem768_*` mirror owners (7 mirrors misplaced — sources
  live under `test/01_unit/app/test/`, mirrors need relocation after the specs
  are fixed)
