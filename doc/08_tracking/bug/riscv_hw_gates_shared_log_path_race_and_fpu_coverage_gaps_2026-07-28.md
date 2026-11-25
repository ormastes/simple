# RISC-V hardware gates: shared log-path race + two FPU coverage gaps

- **Filed:** 2026-07-28
- **Severity:** medium (log race: produces misdiagnosis) / low-medium (coverage gaps)
- **Status:** resolved 2026-11-25 (all three items fixed and injection-verified; see dated section below)
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

## 2026-11-25 resolution (P3 ledger sweep, Windows worktree @ origin/release/1.0.0)

All three items fixed; verified with the tracked `bin/simple.exe` (`SIMPLE_LIB=src`, run path).

**1. Shared log path race — FIXED.** `scripts/check/check-riscv-hardware-gates.shs`
now logs to a unique per-run directory
`build/riscv_hw_gates/run-$(date +%Y%m%d-%H%M%S)-$$` and prints `logs: <dir>`
at startup, so a reported rc and the log a reader opens always come from the
same run. Verified: `sh -n` clean; a live run printed
`logs: build/riscv_hw_gates/run-20261125-185311-58256` and created that dir.

**2. `fpu_probe` canonical-NaN gap — FIXED.** Added check
`FDIV.D 0/0 -> canonical qNaN bits + NV` (fpu_probe.spl §7b), which reads back
the DUT-produced NaN and compares against the literal `0x7FF8000000000000`
(hardcoded, not imported, so a corrupted `CANON_NAN_D` cannot make the check
tautological). Injection-verified both directions: clean source →
`FPU PROBE: ALL PASS`; `CANON_NAN_D` corrupted to `0x7FF8000000000001` (the
exact injection this doc reported undetected) → `FAIL FDIV.D 0/0 -> canonical
qNaN bits + NV`, `1 FAIL`.

**3. `core_fpu_integration_probe` NaN-boxing gap — FIXED, after repairing the
probe itself.** The probe was RED at HEAD before this change, for two
pre-existing staleness reasons: (a) it used `st.rf.regs[N]`, removed when
`RegFile64` was flattened to `reg_0..reg_31` (now uses
`regfile64_read_one(st.rf, N)` like the sibling core64_probe); (b) every FP op
trapped because the core gained spec-compliant mstatus.FS=Off-at-reset gating
(2026-08-11, after this doc was filed) — each FP section now enables
FS=Initial via `csrrw mstatus` first, and §3 enables FS so its trap is
attributable to the DI toggle specifically. With the probe green
(`CORE FPU INTEGRATION: ALL PASS`), added §2c `FMV.W.X NaN-boxes single
(upper32 all ones)`: FMV.W.X then FMV.X.D raw readback through the core must
equal `0xFFFFFFFF00000000 | x`. Injection-verified: `NANBOX_HI` corrupted to
`-0x200000000` (this doc's exact injection) → `FAIL FMV.W.X NaN-boxes single
(upper32 all ones)`, `1 FAIL`; clean source → ALL PASS.

**Limits / out of scope (recorded, not fixed here):**
- Gate-level Simple-probe execution is blocked on this host: the script
  refuses the Rust bootstrap seed (`engine=rust-seed, qualification=unavailable`),
  and ghdl is absent (JTAG tbs FAIL, pre-existing). The two changed probes were
  therefore verified by direct `bin/simple.exe run` invocation.
- The same `rf.regs[...]` staleness that broke `core_fpu_integration_probe`
  also breaks other gate probes at HEAD (`boot64_probe`, `csr_machine_id_probe`,
  `soc_top_64_probe`, `sv39_probe`, `rvfi64_probe`, `bootrom_dtb_probe`,
  `hart_debug_probe`, both `isa_conformance` probes — 10 files total matched).
  That is a separate mechanical-migration defect, not one of this bug's three
  items; it needs its own lane.
