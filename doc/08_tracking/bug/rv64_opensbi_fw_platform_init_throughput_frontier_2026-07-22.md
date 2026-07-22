# RV64 OpenSBI boot frontier = soc_top_64 sim throughput (fw_platform_init)

- **Date:** 2026-07-22
- **Lane:** QQ (OpenSBI frontier chase)
- **Status:** OPEN — out-of-file-set / cross-lane blocker
- **Severity:** medium (blocks reaching the OpenSBI UART banner in-simulation;
  does NOT indicate a correctness defect in the executed path)
- **Owners (files to change):** `src/lib/hardware/rv64gc_rtl/core64.spl` /
  `lsu64.spl` (JIT lowering), `src/lib/hardware/soc_rtl/soc_top_64.spl`
  (per-tick RAM copy). NOT owned by Lane QQ.

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
(→ `sbi_init` → console driver init → banner). Execution continues trap-free into
sbi_init-era code (max_pc reaches `semihosting_init`), but under the sim's
throughput limit + 60 s per-process cap + compacted memory map it does not reach
the banner within a single run. The likely blocker is **simulation throughput**;
a compacted-map artifact or a loop in other-owned code is not yet ruled out (see
"UNVERIFIED" and "Compacted-map caveat" below).

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

**UNVERIFIED — what the next owner must establish.** Whether that flat `max_pc`
means (a) slow-but-forward-progressing execution (perf-bound), (b) a
non-terminating loop in other-owned code, or (c) an artifact of the compacted
sim map (see below) is **not established**. The `max_pc` metric is confounded by
loops (a lower-pc loop keeps `max_pc` flat while still iterating), and I have no
honest-128 MiB data point at this depth to compare against.

### Compacted-map caveat (honesty)

The observable harness trims RAM to 0x70000 and relocates the DTB to
0x80060000. That keeps the executed instruction stream identical for code below
0x48000, BUT any firmware read into `[0x70000, 128 MiB)` returns 0
(`ram64_read` out-of-range → 0). If sbi_init-era code scans/enumerates the
memory region the FDT advertises (128 MiB @ 0x80000000), it would read zeros and
could loop or misbehave in a way that would NOT happen on a full 128 MiB map.
So the in-region looping above may be a trimmed-RAM artifact, not a real hang and
not pure perf. **Confirm on the honest 128 MiB map before concluding.**

## Candidate blockers (both out of Lane QQ's file set — not established root cause)

1. **core64 datapath runs interpreted.** JIT lowering fails with
   `Unknown variable: lsu64_load while lowering core64_combinational`, so every
   tick tree-walks the whole combinational core (~600 ticks/s). Fixing this
   HIR-lowering gap is the most likely lever for the ~10-100x needed to make a
   full-map, banner-depth run tractable.
2. **soc_top_64_tick deep-copies the sim RAM `[i64]` per tick** (value
   semantics). Shrinking RAM 128 MiB -> 0x70000 gave ~16x (27 -> ~600 ticks/s),
   confirming a copy component; the residual is the interpreted core (see #1).

## Reproduce

```
sh scripts/os/build_opensbi_rv64_soc.shs           # builds fw_payload.bin (needs riscv64 cross-gcc)
bin/simple run test/01_unit/lib/hardware/soc_rtl/opensbi_boot_probe.spl   # Case 3 pins the frontier
```

Case 3 of `opensbi_boot_probe.spl` asserts, deterministically and fast (≤9000
ticks): fetch @0x8e == 0x0102bf03 (ram64 fix), and a trap-free boot reaching
`_relocate_done` + bss-zero + `fw_platform_init`.

## Exit criterion

When core64 JIT lowering no longer falls back (or an equivalent speedup lands),
re-run the boot to the banner and promote Case 3 to assert the banner prefix in
`uart_tx`.
