# OpenSBI fw_payload for the RV64 SoC (soc_top_64)

Reproducible OpenSBI build targeting the SoC RTL memory map, plus a sim
loader probe that boots the M-mode payload on the real `core64` datapath.

## Memory map (QEMU virt layout, `wb64_qemu_virt_regions`)

| Region    | Base          | Used by payload |
|-----------|---------------|-----------------|
| DRAM      | `0x8000_0000` | payload text (loaded at offset 0) |
| CLINT     | `0x0200_0000` | `mtime` read @ `0x0200_BFF8` |
| PLIC      | `0x0C00_0000` | not touched by the stub |
| UART16550 | `0x1000_0000` | THR writes (marker string) |

## Build

```sh
sh scripts/os/build_opensbi_rv64_soc.shs                 # stub + OpenSBI v1.4
sh scripts/os/build_opensbi_rv64_soc.shs --payload-only  # stub only (offline)
```

Outputs under `build/os/opensbi_rv64_soc/`:

- `payload_mmode_uart.{S,elf,bin,dis}` — 88-byte M-mode bare payload
  (RV64I-only, position-independent): prints `OSBI-PAYLOAD-OK` to UART THR,
  reads CLINT `mtime` and prints `+` (ticking) or `-` (stuck), newline, spins.
- `fw_payload.{elf,bin}` — real OpenSBI (`PLATFORM=generic`, `FW_PAYLOAD=y`,
  `FW_TEXT_START=0x80000000`, payload = the stub, entry offset `0x20_0000`).
- `opensbi_build.log`, `opensbi-src/` — build log and pinned source clone.

Pin: OpenSBI tag `v1.4`, peeled commit
`a2b255b88918715173942f2c5e1f97ac9e90c877`; the script hard-fails on mismatch.

### Toolchain

- Stub: `riscv64-unknown-elf-gcc` preferred, `riscv64-linux-gnu-gcc` fallback
  (`-march=rv64i -mabi=lp64 -nostdlib`, no compressed insns, no CSRs).
- OpenSBI: `riscv64-linux-gnu-` preferred. Known defect: Ubuntu's
  `riscv64-unknown-elf` binutils 2.42 `ld` rejects `--exclude-libs` (used by
  the OpenSBI Makefile), so the script auto-selects the linux-gnu toolchain
  for the OpenSBI link when present.
- No cross-gcc at all: script exits 2; the loader probe still runs green via
  its embedded hand-encoded copy of the same payload (byte-identical to the
  gcc output, verified against `payload_mmode_uart.dis`).

## Loader probe (gate)

```sh
bin/simple run test/01_unit/lib/hardware/soc_rtl/opensbi_boot_probe.spl
```

Three cases (all must pass; final line `OPENSBI BOOT PROBE: ALL PASS`):

1. **M-mode stub** — writes `payload_mmode_uart.bin` into DRAM via
   `ram64_write`, ticks 300 cycles, asserts `uart_tx ==
   "OSBI-PAYLOAD-OK" + '+' + '\n'` and the spin-loop park PC. Falls back to the
   embedded payload when the build artifact is absent. 100% 32-bit encodings.
2. **Throughput wall removed** — allocates a real 128 MiB DRAM
   (`ram64_init`, doubling fill) and bulk-loads the 2 MiB `fw_payload.bin`
   (`ram64_load_bytes`, word-packing), asserting both complete in seconds and
   the RAM round-trips the first word. Prints the measured numbers.
3. **Real fw_payload boot** — loads `fw_payload.bin` at `0x8000_0000` and the
   SoC DTB (`soc_virt.dtb`) at `a1=0x8800_0000`, sets the boot ABI
   (`a0=0`, `a1=0x8800_0000`), and ticks. Asserts the exact first divergence
   (see below).

## Real-boot result: measured (2026-07-22)

Wall removed (interpreter, this host):

| Step | Before | After |
|------|--------|-------|
| `ram64_init` 128 MiB (16.78 M words) | O(N²) `data = data + [0]` append: minutes/impractical | doubling fill: **~3–4.5 s** |
| Load 2 MiB `fw_payload` | byte-wise RMW loop (per-byte, no word-packing): **~39 s** (measured) | `ram64_load_bytes` word-packing (8 bytes/store): **~2.9–3.7 s** |

(`ram64_write` driven one byte at a time — as Case 1 does for the 88-byte stub —
allocates a fresh state per call and is unsuitable for a 2 MiB blob; it was not
benchmarked at 128 MiB scale. The ~39 s "before" is the byte-mode RMW loader,
the honest baseline the word-packing fast path replaced.)
| `soc_top_64_tick` rate | — | **~300 (shallow) / ~675–800 (deep) ticks/s** |

### Frontier update (2026-07-22, Lane QQ) — boots trap-free into `fw_platform_init`

The two divergences that used to stop the boot are now fixed:

- **RV64C** (Lane PP) — the core decodes compressed instructions and steps
  `pc` by 2 (IALIGN=16). The old `c.li a0,-1` @`0x8000_0548` stall is gone.
- **ram64_read dword-crossing fetch** (Lane QQ) — a 32-bit access whose byte
  address is ≡6 (mod 8) used to drop its top two bytes and sign-extend
  (`ld t5,16(t0)` @`0x8000_008e` fetched `0xFFFF_BF03` instead of `0x0102_bf03`,
  trapping cause 4 inside the ELF relocate loop). `ram64_read` now stitches
  across the 8-byte doubleword boundary with **logical** shifts. Fixed value is
  `0x0102_bf03`, exact.
- **trap-entry IALIGN masks** (Lane QQ) — `trap64_enter_m_only` (`mepc`) and the
  S-mode delegation path (`sepc`) masked the saved PC with `~3`; changed to `~1`
  so a compressed-PC trap return is not misaligned. (`mtvec`/`stvec` keep `~3` —
  those hold the vector BASE with MODE bits `[1:0]`.)

With all three, **real OpenSBI now boots trap-free** (`mcause==0`) through the
compressed `_start`, the ELF `R_RISCV_RELATIVE` relocate loop
(`_relocate_done` @`0x8000_00a4`), the bss-zero loop (@`0x8000_00cc`), and into
**`fw_platform_init`** (FDT platform-init C code, @`0x8000_48ba`) — these four
are hard-asserted in Case 3. Measured: 18 000 / 28 000 ticks both `mcause==0`,
no trap; `max_pc` reaches `0x8000_e4d6` (`semihosting_init`, an sbi_init callee),
so execution continues past `fw_platform_init` into sbi_init-era code.

**Current frontier: the banner is not reached within a single run** (it is ~10⁵
instructions further: `sbi_init` → console init). The **likely** blocker is
simulation throughput — the `soc_top_64` core runs interpreted (core64 JIT
falls back: `Unknown variable: lsu64_load`) at ~600 ticks/s with a per-tick RAM
copy, under the host's ~60 s per-process CPU cap. **Not yet distinguished** from
a compacted-map artifact (the observability harness trims RAM to 0x70000, so
firmware reads ≥0x70000 return 0) or a loop in other-owned code — the next owner
must confirm forward progress on the honest 128 MiB map. Filed:
`doc/08_tracking/bug/rv64_opensbi_fw_platform_init_throughput_frontier_2026-07-22.md`.

### Remaining blockers (past the throughput frontier, unexercised)

Not yet reached — execution is throughput-bound inside `fw_platform_init`:

1. **S-mode / `mret` drop** — OpenSBI's purpose; delegation path present
   (`csr64_update_mip_s`, Sv39) but unexercised by a real firmware run.
2. **PMP** — `sbi_hart_pmp_configure` writes `pmpcfg0`/`pmpaddr0`
   (`0x3A0`/`0x3B0`). CsrExt64 now provides storage for `pmp*`/`menvcfg`
   (`0x30A`)/`mcounteren` (`0x306`) (no enforcement) — predicted to be exercised
   once throughput allows reaching `sbi_hart_init`.
3. **DTB**: supplied — `examples/09_embedded/simple_os/arch/riscv64/soc_virt.dtb`
   (1495 B) matches this SoC (memory@80000000/128 MiB, clint@2000000,
   uart@10000000, model `simple-soc-rv64`).

Board note (board-runnable rule): sim-RTL bring-up lane; the same
`fw_payload.bin` is the artifact a physical RV64 board would flash once the core
gaps above close. No board claim is made here.
