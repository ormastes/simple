# Bug: seed JIT miscompiles soc_top_64 (RV64 SoC) — masked by the lsu64_load/len lowering fallback

- **ID:** seed_jit_miscompiles_soc_top_64_masked_by_fallback
- **Date:** 2026-07-22
- **Status:** OPEN (Rust seed JIT backend; deep, out of pure-Simple scope)
- **Severity:** high — it is the REAL blocker to the OpenSBI banner; supersedes the "lowering fallback" framing
- **Component:** seed JIT codegen (`src/compiler_rust`), not symbol lowering

## Headline
The seed JIT does not merely *fail to lower* the RV64 SoC — when forced to
engage, it **miscompiles** it. The `Unknown variable: lsu64_load` /
`Unknown variable: len` lowering fallbacks were **inadvertently protecting
correctness** by forcing `soc_top_64` onto the (correct) interpreter. Removing
them exposes a pre-existing JIT codegen bug.

## Proof (same worktree, same code, only execution mode differs)
Reaching zero lowering fallbacks needs 4 semantically-identical .spl edits
(1 braced import `use ...lsu.{lsu64_load}`; 3 `len(x)` -> `x.len()` in
ram64.spl/wb64_interconnect.spl). With those applied:
- `SIMPLE_EXECUTION_MODE=interpreter`: `SOC64 PROBE: ALL PASS`.
- default (JIT engages, 0 fallbacks): **`SOC64 PROBE: 57 FAILURES`**, first ones:
  - `FAIL case3 boot handoff lands at 0x80000000`
  - `FAIL case3 sp/a1/t0 zero-extended` (bootrom ABI reads wrong)
  - `FAIL case5 csrrw wrote mtvec` / `handler wrote marker` / `mcause` / `mepc`
  - `FAIL caseh sret: SPIE set to 1 (bit 5)`
- `core64_probe` JITs **correctly** (`CORE64 PROBE: ALL PASS`) — so the miscompile
  is specific to `soc_top_64`'s run-loop / memory / CSR path, not the bare core.

## Boot-level symptom
With JIT engaged the real OpenSBI boot is ~15x faster (300k ticks in ~30 s vs
457 s) but **derails**: `max_pc` collapses to 0x8000000C and pc wanders BELOW
the RAM base (0x7FEC_xxxx) — garbage execution. The correct interpreter reaches
`sbi_hsm_hart_start` (max_pc 0x8001411E). Fast-but-wrong is not usable.

## Consequence for the banner
The banner cannot be reached via "enable the JIT":
1. JIT is fast but miscompiles soc_top_64 (57 probe failures; boot derails).
2. The interpreter is correct but ~15x slower AND, given unlimited time (watchdog
   defeated), still spins in `sbi_hsm_hart_start` near `sbi_hart_hang` — a
   FUNCTIONAL wall, not only speed (see the frontier doc).
Reaching the banner therefore needs EITHER (a) fixing this JIT backend
miscompile (deep, unbounded, risky — the JIT compiles everything), OR (b) the
self-hosted native compiler (the known bootstrap-deploy blocker), AND separately
(c) diagnosing the `sbi_hsm` functional spin. None is a bounded "JIT fix."

## What must NOT be done
Do NOT land the 4 fallback-eliminating .spl edits: they make the buggy JIT
engage and would turn the landed `SOC64 PROBE`/`check-riscv-hardware-gates` from
green to 57 failures. The lowering fallback is currently load-bearing.

## Fix direction (Rust seed JIT backend)
Bisect the soc_top_64 JIT miscompile from the simplest failing case
(`case3 boot handoff` — a memory read returning the boot ABI values). Likely a
codegen bug in a construct soc_top_64 uses that core64 does not (large struct
threading through soc_top_64_run, the DRAM `[i64]` store path, or the MMIO
dispatch). Regression-gate with `SOC64 PROBE` under JIT.

## Cross-refs
[[seed_jit_lsu64_load_lowering_forces_interpreter]] (the lowering symptom this
supersedes) and [[rv64_opensbi_fw_platform_init_throughput_frontier]].
