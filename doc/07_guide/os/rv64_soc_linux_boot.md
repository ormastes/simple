# RV64 SoC Linux Boot — Assets, Addresses, and Remaining Steps

Boot assets for running OpenSBI (and eventually Linux) on the landed Simple
RV64 SoC (`src/lib/hardware/soc_rtl/`), on GHDL/simulation and — per the
board-runnable rule — the K26 board once Lane N's clock/bitstream lands.

## Boot chain and load addresses

Fixed by `bootrom_read64` in `src/lib/hardware/soc_rtl/bootrom.spl`
(reset vector 0x1000; sets `a1`, jumps via `t0`, never returns):

| Addr         | What                | Who puts it there / who jumps |
|--------------|---------------------|-------------------------------|
| `0x00001000` | bootrom             | RTL ROM; sets `a1=0x88000000`, jumps `t0=0x80000000` |
| `0x80000000` | OpenSBI `fw_jump.bin` | preloaded into RAM; OpenSBI jumps to `FW_JUMP_ADDR` |
| `0x80200000` | kernel `Image`      | preloaded; entered S-mode(*) with `a0=hartid`, `a1=dtb` |
| `0x88000000` | `soc_virt.dtb`      | preloaded; `a1` from bootrom, `FW_JUMP_FDT_ADDR` in OpenSBI |
| above kernel | `initramfs.cpio.gz` | optional; advertise via `/chosen` `linux,initrd-start/end` |

(*) S-mode entry requires the core's S-mode support — see Gaps.

## Files

- `examples/09_embedded/simple_os/arch/riscv64/soc_virt.dts` — device tree
  matching the RTL exactly: 1 hart rv64imac, `memory@80000000` (128 MiB —
  must equal `dram_size` passed to `soc_top_64_init`), `clint@2000000`,
  `plic@c000000` (`riscv,plic0`, `ndev=31`, one M-mode context), `uart@10000000`
  (`ns16550a`, byte regs `reg-shift=0`/`reg-io-width=1`, PLIC source 10).
- `scripts/os/build_rv64_linux_assets.shs` — builds into `build/os/rv64_soc/`:
  - default: `soc_virt.dtb` (dtc) + `initramfs.cpio.gz` (freestanding static
    `/init`, `-march=rv64imac -mabi=lp64`, prints `SIMPLE-RV64-INIT OK`) +
    honest `manifest.txt` (each artifact BUILT/MISSING).
  - `--opensbi`: clones pinned OpenSBI v1.4, builds `fw_jump.bin` with
    `PLATFORM_RISCV_ISA=rv64imac_zicsr_zifencei PLATFORM_RISCV_ABI=lp64`,
    `FW_JUMP_ADDR=0x80200000`, `FW_JUMP_FDT_ADDR=0x88000000`.
  - `--kernel`: clones pinned Linux v6.6 stable and builds the rv64 `Image`
    (slow; opt-in). Until run, the manifest lists `Image` as MISSING — no
    fake image is ever produced.

## Clock TODO (blocks final DTB)

`clock-frequency` (UART) and `timebase-frequency` (CLINT `mtime` ticks once
per core clock) are set to the **25 MHz candidate** and marked
`TODO(laneN-clock)` in the DTS. Lane N owns the real PL clock decision
(core closes timing only ≤ ~33 MHz per the WNS probe). When it lands:
update both values in `soc_virt.dts`, rerun the build script.

## ISA note — rv64imac has no F/D

Everything loaded onto this core must be built soft-float:
- OpenSBI: ISA/ABI flags above (already in the script).
- Kernel: build with `CONFIG_FPU=n` (defconfig enables FPU; flip it before
  `Image` is used on the RTL core — QEMU rv64gc masks this mistake).
- Userspace/init: `-march=rv64imac -mabi=lp64` (script does this; a default
  glibc lp64d binary traps on the first FP instruction).

## Gaps to a live Linux boot (fail-closed list)

1. **S-mode in the core** — OpenSBI enters the kernel in S-mode and Linux
   needs Sv39 paging. Lane M's S-mode work must land first; until then the
   chain is provable only through OpenSBI banner + `fw_jump` handoff.
2. **PLIC S-mode context** — `plic.spl` implements one context (context 0 =
   M-mode, ext irq 11). Linux's PLIC driver claims a context whose
   `interrupts-extended` is S-ext (9). Cross-lane request: add context 1
   (S-mode) to the RTL PLIC, then extend `interrupts-extended` in the DTS.
3. **CLINT vs SBI timer** — with S-mode, Linux uses the SBI timer (OpenSBI
   drives `mtimecmp`); no RTL change expected, but unverified.
4. **Kernel image** — run `--kernel` (network + `riscv64-linux-gnu-gcc`
   verified present) with `CONFIG_FPU=n`; then preload the four artifacts at
   the manifest addresses in the GHDL/QEMU harness and on the board flow.
5. **Board** — same artifacts must load on K26 once Lane N's timing-closed
   bitstream exists; QEMU/GHDL-only is not completion (board-runnable rule).

## Verification snapshot (2026-07-22)

- `dtc` compiles `soc_virt.dts` cleanly (1495-byte DTB, zero warnings).
- `fw_jump.bin` 270,768 B built from pinned v1.4 with the exact jump/FDT
  addresses above.
- `/init` verified `ELF 64-bit UCB RISC-V, RVC, soft-float ABI, statically
  linked`.
