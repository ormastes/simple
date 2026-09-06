> **Attribution correction (orchestrator, 2026-07-25).** The shared
> `error: semantic: variable ``hardware`` not found` behind AC-6 and AC-1 is NOT a
> new generator defect. The generators were run with `SIMPLE_BINARY=bin/simple`,
> which is the **Rust bootstrap seed** (`--version` prints the seed banner), and
> the seed's unsupported `@hardware` semantic is already documented in this goal's
> own log (state.md lines 316 and 339).
>
> These ACs are therefore blocked by the SAME upstream cause as everything else:
> there is no self-hosted `bin/simple`, because redeploy is blocked by stage4
> peaking ~111GB. Chain:
>
> stage4 ~111GB → earlyoom kill → no self-hosted binary → seed must be used →
> seed lacks `@hardware` → RTL generators fail → AC-6 and AC-1 fail.
>
> Do NOT file a new generator bug. Fixing stage4 memory is the single upstream
> unblock for the compiler lane AND the FPGA lane.

# RISC-V FPGA Acceptance-Criteria Quick Wins — 2026-07-25

All commands run from repo root, `bin/simple` = pure-Simple self-hosted binary
(`bin/release/x86_64-unknown-linux-gnu/simple`). No commits/pushes made — all
evidence lives in this bundle only.

## AC-6 — regenerate authoritative RTL from tracked .spl sources

Ran (bounded 280s each):
```
SIMPLE_BINARY=bin/simple sh scripts/fpga/generate_rv64_vhdl.shs
SIMPLE_BINARY=bin/simple sh scripts/fpga/generate_rv32_vhdl.shs
```
Evidence: `rv64_gen_run_2026-07-25.log`, `rv32_gen_run_2026-07-25.log`,
`driver.log`, `product_core.log`.

**Result: BLOCKED, both lanes, with a real (non-timeout, immediate)
compiler error** — not a rebuild artifact:

```
error: semantic: variable `hardware` not found
```

This fires inside `rv64_vhdl_driver.spl` / `rv32_vhdl_driver.spl` (the SoC-glue
driver step, before the core compile step even completes) for BOTH
architectures. Step [2/4], compiling
`src/lib/hardware/rv64gc_rtl/imac_entry.spl` via
`src/app/cli/vhdl_compile_entry.spl`, did not finish inside the 280s bound
(killed by timeout, inconclusive — not evidence of failure by itself). Step
[3/4] file-presence check confirms the existing `build/vhdl/rv64/*.vhd` tree
is stale/partial versus the generator's current expected-file list: it is
MISSING `rv64gc_core_product.vhd`, `rv64gc_core_product_wb.vhd`,
`uart16550.vhd`, `soc_top_rv64_external_ddr.vhd`, `wb64_axi_hp_bridge.vhd`,
`soc_top_rv64_k26_pl.vhd` — i.e. the on-disk `.vhd` predates the generator's
own current expected-output contract, independent of the freshness-vs-source
question in the task brief.

**AC-6 verdict: NOT MET.** The generator cannot currently regenerate the RTL
at all (real semantic error, reproduced twice), so freshness cannot be
re-established by this lane. This is a generator/driver defect, not a
missing-evidence gap — worth filing as a bug.

**AC-12 (source-map sidecars):** confirmed zero `.map.json` / `.gen.json`
files exist anywhere in the repo (`find . -iname '*.map.json' -o -iname
'*.gen.json'` → 0 hits). The generator does not emit them. This is a real
AC-12 gap, not a search miss.

## AC-1 — RTL smoke gate, saved output

Ran: `sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=200`
(280s outer bound). Evidence: `rtl_smoke_run_2026-07-25.log` (full, 1027
lines).

**Result:**
```
FAIL generated_rv32_linux smoke
FAIL generated_rv64_linux smoke
```
Both lanes fail with the identical root cause as AC-6:
`error: semantic: variable \`hardware\` not found`, thrown while compiling
`src/lib/hardware/riscv_common/pkg/riscv_generated_core_pkg.spl` (line 81,
`self.xlen_bits`) via the same generated-RTL Linux-smoke path.

**AC-1 verdict: NOT MET.** The log-claimed "passes both lanes" is
contradicted by this run — both lanes FAIL, same systemic cause as AC-6.

## AC-3 / AC-5 — preflight snapshot

Ran `--local-only` (no board programming):
```
sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs --local-only
sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only
```
Evidence: `preflight_rv64_run_2026-07-25.log`,
`preflight_dual_run_2026-07-25.log`, dated snapshot doc
`rv64_fpga_simpleos_preflight_snapshot_2026-07-25.md` (bundle copy of what
would land in `doc/09_report/`).

**Result:** tool/board environment all PASS (FT4232H present, JTAG free, 2
serial ports, openFPGALoader/OpenOCD/Vivado/Yosys found, both RISC-V
cross-gcc toolchains found). But pipeline checks fail: rv64 lane 10 failures
(missing ELF/bin/bitstream artifacts, stale bitstream, missing product PS-DDR
RTL, missing/stale GHDL DUT proof, zero synth utilization, no board
load/run/login-ls evidence, no decoded GHDL marker); dual-arch run adds 8 more
rv32-specific failures of the same classes.

**AC-3/AC-5 verdict: recording gap CLOSED** (dated snapshot now exists with
real tool/board/artifact/JTAG/UART/bitstream status), **but the underlying
pipeline is NOT green** — 18 total FAILs recorded honestly, not glossed over.

## Summary

| AC | Verdict | Decisive line |
|----|---------|----------------|
| AC-6 | NOT MET / BLOCKED | `error: semantic: variable \`hardware\` not found` (both rv32 and rv64 generators, reproduced) |
| AC-1 | NOT MET | `FAIL generated_rv32_linux smoke` / `FAIL generated_rv64_linux smoke` |
| AC-3/AC-5 | Snapshot gap CLOSED; pipeline NOT MET | rv64: `preflight_failures=10`; dual-arch: `dual_arch_preflight_failures=8` |
