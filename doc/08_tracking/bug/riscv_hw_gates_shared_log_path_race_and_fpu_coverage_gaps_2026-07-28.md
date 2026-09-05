# RISC-V hardware gates: shared log-path race + two FPU coverage gaps

- **Filed:** 2026-07-28
- **Severity:** medium (log race: produces misdiagnosis) / low-medium (coverage gaps)
- **Status:** open
- **Found via:** Lane R3 gate-honesty audit

## 1. Shared log path makes the reported exit code and the log disagree

`check-riscv-hardware-gates.shs` writes every probe log to a fixed path,
`build/riscv_hw_gates/<name>.log`, and the repo is a shared working copy with
several sessions running the same gates concurrently. Two runs of the same probe
overwrite each other's log, so the `rc` the script reports and the log content a
reader inspects can come from **different runs**.

Observed 2026-07-28: a gate run reported
`FAIL probe addr4g_probe -- rc=2 or no 'ALL PASS'` while
`build/riscv_hw_gates/addr4g_probe.log` showed every check `PASS` and
`ADDR4G_PROBE: ALL PASS`. This is the diagnostic path that fed §1.2 of
`doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-28.md`.

Related: these probes return their failure count as the process exit status
(1 failure -> rc=1, 2 failures -> rc=2, verified by injection). So the plan's
`rc=2` corresponded exactly to the two DTB sub-check failures — the log was the
stale half, not the exit code.

**Fix:** make the log path unique per run (pid/timestamp) or take an exclusive
lock, so a reported failure is always accompanied by the log that produced it.

## 2. `fpu_probe` does not detect a corrupted canonical NaN

`CANON_NAN_D` (`src/lib/hardware/rv64gc_rtl/fpu.spl:63`) is the canonical qNaN
the FPU *produces* on invalid operations (written at fpu.spl:346, 361, 407).
`fpu_probe` only ever supplies `0x7FF8000000000000` as an **input** and checks
the integer result and NV flag; it never reads back a DUT-produced NaN.

Injection: `CANON_NAN_D` -> `0x7FF8000000000001`, probe still exits 0 with
`ALL PASS`. (Control: injecting `W_MAX 0x7FFFFFFF -> 0x7FFFFFFE`, which *is* in
scope, correctly fails with `FAIL FCVT.W.D(NaN)->INT32_MAX + NV`.)

## 3. `core_fpu_integration_probe` does not detect corrupted NaN-boxing

`NANBOX_HI` (`fpu.spl:65`) governs single-precision NaN-boxing. The probe
asserts FMV/FSGNJN/FCVT round-trips but never a boxed single.

Injection: `NANBOX_HI` `-0x100000000` -> `-0x200000000`, probe still exits 0
with `ALL PASS`. (Control: breaking the FSGNJN rm decode correctly fails with
`FAIL FSGNJN.D set sign bit`.)

Both probes gate correctly on defects inside their stated coverage, so these are
**coverage gaps, not fail-open gates**. Add a canonical-NaN readback assertion
and a NaN-boxing assertion to close them.
