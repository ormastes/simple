# System-spec helper file-reads return empty once a spec crosses ~14 tests (2026-11-05)

Status: OPEN — reported by the riscv32-codegen lane (2026-11-05), minimal
unit-spec repro DID NOT reproduce; needs the original system-spec shape.

## Symptom
`test/system/simpleos_riscv_network_gate_spec.spl` T16/T17: all 14 pinned
script-content markers were verified present on disk, and 13-test subsets of
the same spec PASS, but the full spec (21+ tests) fails with helper file-reads
returning empty content. Adding a trivial 15th test to a passing 14-test
subset re-triggers the empties; removing tests restores the reads.

## Bisect evidence (lane agent, 2026-11-05)
- 13-test subsets: PASS in identical-content form.
- 14+ tests: helper `read_file_text`-class calls return "" (or nil) inside
  helper functions; assertions on the read content then fail.
- Observed only in test/system (system runner path). A 15-example unit-spec
  probe with the same helper pattern passed 15/15 under the unit runner, so
  the trigger is NOT raw example count alone — it likely involves the system
  runner's fork/isolation mode or per-test working-directory reset.

## Reproducer sketch (unverified)
Take test/system/simpleos_riscv_network_gate_spec.spl, delete tests down to
13 (passes), add one back (fails) — content-independent.

## Impact
System specs that read repo files inside helper functions can silently lose
their evidence inputs at scale; green subsets may not compose into a green
whole spec. Suspected seed-runtime/test-runner resource or isolation issue,
NOT a spec-content issue.

## Next step
Reproduce under `--mode=interpreter` vs default system mode with the real
spec, then audit the system runner's per-test process/env reset for file-read
facade state (rt_io file cache, cwd).

## 2026-11-05 follow-up evidence (network-gate lane)
The trigger is NOT purely example count: identical 13-test subsets of
test/system/simpleos_riscv_network_gate_spec.spl differing only in the `it`
name string diverge — an RV64-named copy passes while an RV32-named copy fails
file-reads, both pointed at the same rv64 script file. T16 additionally turned
out to be a real spec defect (helper called with a missing `qemu/` path
prefix) that only mimicked the runner bug; after fixing it, T17 alone remains
runner-blocked with empty helper file-reads. This points at name/state-
correlated per-test isolation state in the system runner, not a resource cap.
