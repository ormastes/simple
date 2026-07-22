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

Reads `payload_mmode_uart.bin`, writes it into `soc_top_64` DRAM at
`0x8000_0000` via `ram64_write`, sets `pc`, ticks 300 cycles, then asserts
`uart_tx == "OSBI-PAYLOAD-OK" + '+' + '\n'` and the spin-loop park PC.
Prints `OPENSBI BOOT PROBE: ALL PASS` on success. Falls back to the embedded
payload when the build artifact is absent (source is printed either way).

## Gap to booting real OpenSBI on soc_top_64

The sim boots the M-mode stub, not `fw_payload.bin`. Blockers, in order:

1. **S-mode**: `soc_top_64` interrupt/trap routing is M-mode-only
   (`trap64_enter_m_only`; no delegation, no `sret` path exercised). OpenSBI's
   entire purpose is dropping to S-mode via `mret`.
2. **PMP**: OpenSBI generic programs PMP CSRs at init; the runnable core path
   has no PMP (`memory_access`/`pmp`/`pmp_csr` modules absent — see
   `soc_top_64.spl` header).
3. **DTB**: `PLATFORM=generic` parses a device tree passed in `a1`; the sim
   provides none. A minimal baked DTB (RAM+CLINT+PLIC+UART) is needed.
4. **ISA breadth**: OpenSBI uses CSRs/fences/compressed insns well beyond the
   stub's RV64I subset; needs difftest-grade coverage before a 2 MB firmware
   run is debuggable.
5. **Sim throughput**: `fw_payload.bin` is 2,097,256 bytes; byte-wise
   `ram64_write` loading plus millions of boot cycles in the interpreter is
   impractical today — a bulk RAM-load helper and a faster tick path would be
   prerequisites.

When those close, the built `fw_payload.elf/.bin` from this script is the
artifact to boot — no build-side changes should be needed.

Board note (board-runnable rule): this is a sim-RTL bring-up lane; the same
`fw_payload.bin` is the artifact a physical RV64 board would flash once the
core gaps above close. No board claim is made here.
