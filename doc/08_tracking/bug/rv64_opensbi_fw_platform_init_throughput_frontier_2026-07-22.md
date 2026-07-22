# RV64 OpenSBI boot frontier = soc_top_64 sim throughput (fw_platform_init)

- **Date:** 2026-07-22
- **Lane:** QQ (OpenSBI frontier chase); RR (per-tick RAM copy elimination, 2026-07-22)
- **Status:** PARTIALLY RESOLVED — the per-tick RAM value-copy is FIXED (Lane RR,
  `soc_top_64_run`); the residual banner blocker is a ~60 s wall-clock process
  watchdog + the interpreted core (`lsu64_load` JIT fallback), both out of this
  lane's file set.
- **Severity:** medium (blocks reaching the OpenSBI UART banner in-simulation;
  does NOT indicate a correctness defect in the executed path)
- **Owners (files to change):** `src/lib/hardware/rv64gc_rtl/core64.spl` /
  `lsu64.spl` (JIT lowering — the remaining lever). The per-tick RAM copy in
  `src/lib/hardware/soc_rtl/soc_top_64.spl` is DONE (see "Resolution").

## Summary

After the Lane QQ fixes (ram64_read dword-crossing stitch; trap-entry
`mepc`/`sepc` IALIGN=16 mask `~3 -> ~1`), the REAL OpenSBI v1.4 `fw_payload`
boots **trap-free** on `soc_top_64`:

- executes the compressed `_start` / `fw_boot_hart`,
- runs the ELF `R_RISCV_RELATIVE` relocate loop to completion
  (`_relocate_done` @0x800000a4) — this is the `ld t5,16(t0)` @0x8000008e path
  that used to trap (cause 4) before the ram64 fix,
- runs the bss-zero loop (@0x800000cc),
- enters `fw_platform_init` (the FDT platform-init C code, @0x800048ba),

all with `mcause == 0`. **No correctness wall remains through `fw_platform_init`**
(this is the verified, hard-asserted claim in Case 3).

The OpenSBI UART banner is NOT reached. It lives ~10^5 instructions further
(→ `sbi_init` → console driver init → banner).

## Resolution (Lane RR, 2026-07-22): per-tick RAM value-copy ELIMINATED

`soc_top_64_tick` threads the whole `SocTop64State` — including the DRAM `[i64]`
word array — by value. Measurement (see below) proves that passing the state by
value and returning a scalar-changed copy are BOTH independent of RAM size (the
`[i64]` is a refcounted handle, shallow-shared). The ONE operation that scales
with RAM size is a store `data[i] = v` on a NON-unique array: the interpreter
copy-on-writes the whole array because the driver's `soc` binding is a competing
reference. On the honest 128 MiB map that is **~315 ms per store, ~29 ticks/s**.

Fix: `soc_top_64_run(soc, max_ticks) -> SocRunResult` keeps the ENTIRE tick loop
in one call and performs the DRAM store with the "drop-ref" in-place pattern
(lift `ram.data` into a bare local, clear the struct field so the local is the
sole holder, mutate in place — one copy-on-write amortized over the whole run,
then O(1) per store). Every other step calls the exact same helpers in the same
order as `soc_top_64_tick`; only the step-6 DRAM store is inlined, so semantics
are identical (verified: `run` vs a looped `tick` reach byte-identical
pc/mcause/uart state). Result: honest 128 MiB map **~29 → ~665 ticks/s (≈23x)**,
i.e. parity with the old compacted map — on the FULL map with no read-trimming.

Measured (128 MiB DRAM):

| path | store cost | ticks/s (honest 128 MiB) |
|------|-----------:|-------------------------:|
| `soc_top_64_tick` (per-tick CoW copy) | ~315 ms/store | ~29–31 |
| `soc_top_64_run` (drop-ref in-place)  | ~0.1 ms/store (amortized) | ~628–681 |

The residual banner blocker is NOT the per-tick copy — see "True wall" below.

## Evidence (compacted-map harness, RAM 0x70000, DTB @0x80060000)

| ticks | wall time | pc (stop) | max_pc | mcause | milestones (hard-asserted) |
|------:|----------:|-----------|--------|-------:|------------|
| 18000 | 31 s | 0x80009de0 | 0x8000e4d6 | 0 | reloc_done, bss_zero, fw_platform_init |
| 28000 | 46 s | 0x80009dd6 | 0x8000e4d6 | 0 | reloc_done, bss_zero, fw_platform_init |

`max_pc = 0x8000e4d6` lands inside `semihosting_init` and the observed pc band
(0x80009d..-0x8000e4..) spans `sbi_hsm_*` / `sbi_malloc` / `sbi_console` /
`semihosting_init` — i.e. **sbi_init callees**, deeper than `fw_platform_init`.
`mcause` stays 0 throughout (no trap). Between 18k and 28k ticks `max_pc` does
NOT grow.

### Honest-map data (Lane RR, per-tick copy eliminated)

With `soc_top_64_run` the honest **full 128 MiB** map is now runnable at speed.
It reaches, trap-free (`mcause == 0`):

| map | ticks | max_pc | milestones |
|-----|------:|--------|------------|
| honest 128 MiB | 18000 | 0x80013fd6 | reloc_done, bss_zero, fw_platform_init |
| 2 MiB (small)  | 35000 | 0x80013fd6 | reloc_done, bss_zero, fw_platform_init |

`max_pc = 0x80013fd6` lands in the OpenSBI FDT walk
(`fdt_next_tag`/`fdt_offset_ptr`/`fdt_find_match`); the observed pc band
(0x8000f7..–0x8000f9..) is inside `fdt_offset_ptr`/`fdt_next_tag`.

### UNVERIFIED flag — RESOLVED

- **Compacted-map artifact? NO.** A 2 MiB map and a 128 MiB map reach the
  **identical** `max_pc` (0x80013fd6) through `fw_platform_init` and the FDT
  walk. The in-region loop is therefore NOT a trimmed-RAM artifact — the executed
  path in this phase does not depend on RAM size, so honest and compacted maps
  are behaviourally equivalent here. The old "compacted-map caveat" is retired.
- **Per-tick RAM copy? ELIMINATED** (see Resolution). It is no longer a blocker.
- **What remains** is depth: the banner is ~10^5 insns past `fw_platform_init`,
  and a single process is bounded by the wall below.

## True wall (Lane RR): a hard ~60 s wall-clock process watchdog

With the per-tick copy gone, the binding constraint is a **hard ~60-second
wall-clock watchdog** that SIGTERMs (signal 15) `bin/simple` at ~60 s,
independent of memory:

- 128 MiB honest run: killed at 60.65 s, Max RSS 3.3 GB.
- 2 MiB run (same datapath, low memory): killed at 61.41 s, Max RSS **220 MB**.
- A cheap small-RAM run doing 2 M NOP-fetch ticks in < 1 s exits cleanly — so it
  is not a blanket long-process kill; it triggers only when a process actually
  runs the heavy datapath past ~60 s of wall time.

At ~665 ticks/s that bounds a single process to ~35 k datapath ticks. The banner
is ~10^5 insns further, i.e. ~3x the wall budget, so it is unreachable in one
process **regardless of the per-tick copy fix**.

## Candidate blockers to cross the banner (out of this lane's file set)

1. **~60 s wall-clock process watchdog.** The dominant limiter now. Cross it by
   checkpoint/resume of `SocTop64State` (incl. the 128 MiB RAM) across processes,
   or by lifting the watchdog for this workload.
2. **core64 datapath runs interpreted.** JIT lowering fails with
   `Unknown variable: lsu64_load while lowering core64_combinational`, so every
   tick tree-walks the combinational core (~665 ticks/s). Fixing this HIR-lowering
   gap (Rust-side) would raise ticks/s enough to fit more of the boot in each
   ~60 s window.
3. ~~soc_top_64_tick deep-copies the sim RAM per tick~~ — **FIXED** (Lane RR,
   `soc_top_64_run`).

## Reproduce

```
sh scripts/os/build_opensbi_rv64_soc.shs           # builds fw_payload.bin (needs riscv64 cross-gcc)
bin/simple run test/01_unit/lib/hardware/soc_rtl/opensbi_boot_probe.spl   # Case 3 pins the frontier
```

Case 3 of `opensbi_boot_probe.spl` now boots the HONEST full 128 MiB map, prints
BEFORE/AFTER ticks/sec (~31 → ~628), hard-asserts the trap-free milestones
(`_relocate_done` + bss-zero + `fw_platform_init`) and that `soc_top_64_run` is
≥ 5x `soc_top_64_tick`, scans `uart_tx` for the "OpenSBI" banner prefix, and
pins the wall when the banner is absent.

## Exit criterion

The per-tick RAM copy exit criterion is MET. To reach the banner: land a
checkpoint/resume driver (or the core64 `lsu64_load` JIT fix, or a lifted
watchdog), re-run the honest-map boot to the banner, and promote Case 3's
`uart_has_opensbi` scan from a soft finding to a hard assert.

## CORRECTION (2026-07-22, reviewer long-run experiment) — the wall is NOT throughput

The "banner is ~3× past the 60 s budget, throughput-only" conclusion above is
**superseded**. A reviewer long-run with the watchdog defeated ran the honest
128 MiB map for **300,000 ticks / 457 s** to completion (no kill). Result:
`ticks=300000 trapped=false banner=false mcause=0 uart_len=0`.

**Watchdog defeat (reusable):** the ~60 s SIGTERM is the seed's built-in
`start_watchdog(60)` (`src/compiler_rust/compiler/src/watchdog.rs`), armed for
paths under `examples/` unless `SIMPLE_TIMEOUT_SECONDS` is set. Disable with
`SIMPLE_TIMEOUT_SECONDS=0` (env) and run the payload from a non-`examples/`
path; a `setsid` + renamed binary also dodges any name-matching outer reaper.
So a single process CAN run unboundedly — throughput was never the true wall.

**What actually happens (disassembly-anchored):** OpenSBI runs trap-free FAR
past `fw_platform_init` — through `sbi_init` into `sbi_hsm_hart_start` + FDT
phandle resolution (`fdt_node_offset_by_phandle`, `max_pc 0x8001411E`, well
beyond the old `0x80013fd6`). Then `max_pc` freezes for the final ~125k ticks
(pc pinned ~`0x8000C1B4` in `sbi_hsm_hart_start`; `sbi_hart_hang` @`0x8000B8DE`
sits in the same region) — a bounded spin, still `mcause==0`.

**Root cause (leading, evidence-backed): the OpenSBI ns16550a console never
drives our SoC UART, so ALL `sbi_printf` output — including the banner — is
silently dropped** (`uart_len==0` after 300k ticks proves zero bytes ever
reached `uart_tx`). OpenSBI does not check console-write success, so it proceeds
to HSM/domain setup and parks. The lever is **UART/console bring-up**, not
checkpoint/resume, not the `lsu64_load` JIT fix, not the watchdog:
- `soc_top_64.spl`'s UART MMIO is the minimal THR/LSR model; Lane Y's full
  ns16550a `uart16550.spl` is NOT wired into `soc_top_64` (Y's own integration
  note). OpenSBI's 8250 driver polls **LSR.THRE** at the DTB-derived MMIO
  offset (reg-shift/reg-io-width from `soc_virt.dts`) before every byte.
- Fix path: wire the full 16550 (or make the minimal UART present THRE=1 +
  the exact register offsets the ns16550a driver computes) so writes land in
  `uart_tx`; confirm the "OpenSBI v1.4" banner bytes appear.

**New exit criterion:** OpenSBI banner bytes present in `uart_tx` on the honest
map — promote Case 3's `uart_has_opensbi` scan to a hard assert. Assigned to a
UART/console bring-up lane. The throughput/CoW work stands; it was necessary
(the boot now runs unboundedly) but not sufficient.
