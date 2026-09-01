# Running SimpleOS on the Simple RISC-V soft-core (FPGA)

How to boot SimpleOS on the **Simple-generated RISC-V soft-core** (rv32 / rv64) —
first in GHDL simulation (the early-bug-finding gate), then on the Kria KV260
(xck26) board. QEMU proves the *kernel*; the soft-core proves the *hardware*.

> Status (2026-07-25): **rv32 SimpleOS boots to `TEST PASSED` in GHDL** on
> `rv32_exec_core_flat.vhd`, difftest-clean vs QEMU. rv64 bring-up is in progress
> (M-mode-direct, no MMU). On-silicon boot needs the DDR/AXI RAM bridge below.

## 1. What runs where

| Lane | Core | State |
|------|------|-------|
| QEMU rv32/rv64 | (emulated) | SimpleOS boot + ls + launch **green** |
| **GHDL rv32** | `rv32_exec_core_flat.vhd` | **full boot → `SIMPLEOS_RISCV_SMF_FS_PASS` / `TEST PASSED`** |
| GHDL rv64 | `rv64_exec_core_flat.vhd` | bring-up (RV64C decoder port + 74 MB RAM) |
| Silicon (KV260) | flat core → PS-DDR/AXI | roadmap (§6) |

The rv32 core itself was first hardened by running the **minimal NVMe firmware**
against it under a QEMU↔GHDL per-instruction difftest, which found and fixed
three real core RTL bugs (§4) before the OS was ever booted.

## 2. SoC architecture (flat core)

`examples/09_embedded/fpga_riscv/rtl/rv32_exec_core_flat.vhd` is a single-hart
RV32IMC core with a **flat unified RAM** replacing the original 64 KB-ceiling
BRAM. Key facts:

- **Reset PC** `0x8000_0000`, M-mode direct (no OpenSBI, no MMU — SimpleOS rv32
  runs bare-mode physical addressing).
- **Address decode** widened from 14-bit (`off(15 downto 2)`, 64 KB) to 24-bit
  (`off(23 downto 2)`, 16 MB). SimpleOS needs ~8.19 MB contiguous RAM
  (`sp = _stack_top = 0x8081_d010`; `.bss` to `0x8001_d004` incl. a 64 KB heap).
- **UART** 16550 at `0x1000_0000` (TX) / `0x1000_0005` (LSR returns `0x60`
  = THRE|TEMT).
- **Ramdisk bank** (read-only) at `0x8800_0000` — a small FAT32 image preloaded
  from `rv32_ramdisk.mem` (see §3). `a1 = 0x8800_0000` is already returned by
  `rt_rv32_probe_store_a1`.

Memory map:

| Range | Purpose |
|-------|---------|
| `0x8000_0000` + | code + data + bss + stack (flat RAM, 16 MB) |
| `0x1000_0000` | 16550 UART (TX / LSR) |
| `0x8800_0000` | FAT32 ramdisk image (read-only bank) |

## 3. Storage without virtio: the ramdisk trick

SimpleOS's FS is a FAT32 image the kernel normally reaches through a
**virtio-blk-mmio** device (full virtqueue/DMA) — far too much RTL for a soft
core. Instead, all FS access funnels through **one** function,
`virtio_blk_read_sector(lba)` in
`examples/09_embedded/simple_os/arch/common/riscv_common.h`. That function now
**runtime auto-detects** a FAT boot signature (`0xEB`/`0xE9` + `0x55AA`) at
`RISCV_RAMDISK_BASE = 0x8800_0000`; when present it serves 512-byte sectors by a
plain memcpy from that RAM window, otherwise it falls back to the virtio path.

Consequences:

- **One kernel binary serves both lanes** — QEMU (virtio drive) and FPGA
  (ramdisk) — with no build flag and no seed rebuild. The signature check picks
  the backend at runtime.
- Every `fat32_*` / nvfs / smf caller stays device-agnostic via `sector_data()`.
- On silicon the same auto-detect works: populate DDR at `0x8800_0000` with the
  image, then boot.

The GHDL bank is a 1 MiB truncation of `build/os/fat32-riscv32.img` (the smoke
files — `NVFSVER.TXT`, `hello_world.smf`, `browser_demo.smf` — all live in the
first ~0.29 MiB).

## 4. Core RTL bugs found + fixed (via NVMe-fw difftest)

Running the NVMe firmware under a QEMU↔GHDL per-instruction register-trace
difftest surfaced three genuine bugs in `rv32_exec_core.vhd` (carried into the
flat core), all now fixed:

1. **Compressed CA-format ALU mis-decode** — `C.SUB/C.XOR/C.OR/C.AND/C.SRAI` all
   executed as `C.SRLI` (only `h(12)` was decoded). Fix: decode `h(11:10)` +
   `h(6:5)`.
2. **`XORI` unimplemented** — OP-IMM `funct3="100"` fell through to `null`.
3. **`C.LW`/`C.SW` immediate mis-decode** — CL/CS word offset mis-mapped, so
   offset 4 addressed as `0x40`; surfaced only where a correctly-addressed store
   met the buggy load.

After these, the NVMe fw matches QEMU register-for-register across 39,992
instructions, and SimpleOS boots with **no further core divergence**.

## 5. Reproduce (rv32, GHDL)

```bash
# Boots the SimpleOS rv32 kernel on the flat soft-core in GHDL, ramdisk-backed FS.
sh scripts/fpga/ghdl_rv32_simpleos_boot.shs
```

The script flattens a 1 MiB slice of the FAT32 image into `rv32_ramdisk.mem`,
preloads it at `0x8800_0000`, elaborates `tb_rv32_simpleos_boot.vhd` +
`rv32_exec_core_flat.vhd`, and runs. Expected UART transcript:

```
=== SimpleOS RV32 smoke boot ===
[harden] canary arch=riscv32 value=...
SimpleOS RV32 boot OK
[riscv-nvfs] image read ok
FS_MOUNT_OK
SMF_DISCOVERY_OK                              # ls
ELF_LOAD_OK arch=riscv32 app=/sys/apps/hello_world.smf
SMF_CLI_LAUNCH_OK app=/sys/apps/hello_world.smf   # launch
SMF_WM_GUI_LAUNCH_OK app=/sys/apps/browser_demo.smf wm=manifest
NATIVE_GUI_PROCESS_RENDER_OK app=/sys/apps/browser_demo.smf pid=1002
SIMPLEOS_RISCV_SMF_FS_PASS
TEST PASSED
```

Rebuilding the kernel (only if you change the C stubs / `riscv_common.h`): the
boot `*.c` are compiled by the **Rust seed** linker
(`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`,
`link_objects_freestanding`), not the self-hosted `bin/simple`. Build via
`SIMPLE_BOOT_MINIMAL=1 <seed> native-build --backend llvm --entry
examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl --target
riscv32-unknown-none`, and force-clean with
`rm -f build/os/simpleos_riscv32_smf_fs.elf{,.build_stamp}`.

## 6. Path to silicon (KV260, xck26)

The GHDL RAM is a behavioral array; on-silicon it must become real memory:

1. **RAM → PS-DDR via AXI HP.** ~2.8 MB on-chip BRAM ≪ the 8 MB stack; route the
   flat core's load/store port to the Zynq PS DDR4 through an AXI-HP bridge.
   Place the ramdisk image in DDR at `0x8800_0000` (the auto-detect is unchanged).
2. **Synthesize** one bitstream (Vivado 2025.2, `scripts/fpga/build_k26_rv32.shs`
   pattern). One critical-path build at a time — see
   [vivado_device_setup.md](vivado_device_setup.md).
3. **Boot + read markers** over JTAG-MMIO — the PL UART is not routed to a host
   port on the KV260 carrier (see
   [simple_riscv_jtag_debugging.md](simple_riscv_jtag_debugging.md)); read the
   boot/FS markers via `scripts/fpga/read_rv32_core_jtag.shs`, or wire an
   external 3.3 V UART to PMOD J2 (TX=H12, RX=E10).

## 7. rv64

The rv64 SimpleOS kernel (`build/os/simpleos_riscv64_smf_fs.elf`, entry
`0x8020_0000`) executes **zero privileged instructions** — no `satp`, `csr*`,
`sret/mret/ecall`, or `sfence` — so it boots **M-mode-direct like rv32, with no
MMU / Sv39 page-table walker**. QEMU's `-bios default` OpenSBI is only a
chain-loader to `0x8020_0000`. Bring-up mirrors rv32:
`rv64_exec_core_flat.vhd` = 64-bit datapath + the RV32→RV64 **C-extension decoder
port** (the main new work; RV64C differs: `C.JAL`→`C.ADDIW`, `C.FLW/FSW`→`C.LD/SD`,
6-bit shamt) + ~74 MB flat RAM (0x8020_0000 → ~0x84a1_f000 incl. 64 MB heap) +
the same ramdisk bank. FPU is a *false* gap (the `fld` bytes are misdisassembled
address constants). See `doc/09_report/rv64_simpleos_ghdl_soc_scope_2026-07-25.md`.

## Related

- [kv260_rv64gc_fpga_boot.md](kv260_rv64gc_fpga_boot.md) — KV260 rv64gc bring-up
- [simple_riscv_jtag_debugging.md](simple_riscv_jtag_debugging.md) — JTAG-MMIO readout
- [vivado_device_setup.md](vivado_device_setup.md) — Vivado / hw_server
- `.claude/rules/board-runnable.md` — QEMU is the harness, the board is the target
- RTL: `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core_flat.vhd`,
  `tb_rv32_simpleos_boot.vhd`; runner `scripts/fpga/ghdl_rv32_simpleos_boot.shs`
