# Running SimpleOS on the Simple RISC-V soft-core (FPGA)

How to boot SimpleOS on the **Simple-generated RISC-V soft-core** (rv32 / rv64) —
first in GHDL simulation (the early-bug-finding gate), then on the Kria KV260
(xck26) board. QEMU proves the *kernel*; the soft-core proves the *hardware*.

> Status (2026-07-26): **rv32 SimpleOS boots to `TEST PASSED` on REAL KV260
> silicon on TWO paths** — PS-DDR4 (`747c27de111`) and BRAM-only tiny config
> (`0331115d223`, no DDR / no block design / no FSBL). All four sim cores
> (rv32/rv64 × flat/AXI) pass in GHDL. rv64 silicon bring-up in progress.

## 1. What runs where

| Lane | Core | State |
|------|------|-------|
| QEMU rv32/rv64 | (emulated) | SimpleOS boot + ls + launch **green** |
| GHDL rv32 | `rv32_exec_core_flat.vhd` / `rv32_exec_core_axi.vhd` | **full boot → `TEST PASSED`** |
| GHDL rv64 | `rv64_exec_core_flat.vhd` / `rv64_exec_core_axi.vhd` | **full boot → `TEST PASSED`** |
| **Silicon KV260, DDR** | `soc_top_rv32_k26_ddr.vhd` → PS-DDR4 via AXI-HP | **`TEST PASSED`** (446-byte chain, byte-matching GHDL) |
| **Silicon KV260, BRAM** | `soc_top_rv32_tiny_bram.vhd`, 125.5/144 BRAM36 | **`TEST PASSED`** (568 bytes, soft-reset re-run passes) |
| Silicon KV260, rv64 | `soc_top_rv64_k26_ddr.vhd` | bring-up in progress (bitstream timing MET) |

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

## 6. Launching SimpleOS on KV260 silicon (both paths PROVEN 2026-07-26)

Both lanes end at the same bar: full UART marker chain to `TEST PASSED`,
byte-matching the GHDL rehearsal, from a persisted log.

### 6a. DDR lane (full 8 MB kernel from PS-DDR4)

```bash
# 1. GHDL rehearsal of the EXACT silicon SoC — run BOTH plain and garbage-fill:
sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs                 # ~125 ms sim time
GARBAGE_FILL=1 sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs  # unmasks .bss-class bugs

# 2. Bitstream (Vivado 2025.2; ONE heavy build machine-wide):
sh scripts/fpga/build_k26_rv32_ddr_bitstream.shs

# 3. Board bring-up — MUST run with bash (sources settings64.sh):
bash scripts/fpga/bringup_kv260_rv32_ddr.shs > run.log 2>&1
```

The bring-up script does, in order — every step is load-bearing:
1. **Full `psu_init` from the XSA BEFORE `fpga -file`** — without it the S_AXI_HP
   ports are dead and every AXI read returns `0x00000000` (even hardwired regs).
2. Reset all four A53s, program the PL, remove PS-PL isolation.
3. `dow -data` kernel → DDR `0x1000_0000` (core sees `0x8000_0000` via the
   adapter's address translation) and ramdisk → `0x1800_0000` (core
   `0x8800_0000`); verify words back (`DDR_KERNEL_WORD0`, `DDR_BANNER_WORD`).
4. **Zero `.bss`** (`ZEROING_BSS`, with `BSS_HEAPOFF_PRE/POST` readback). Real
   DDR powers up as garbage; GHDL RAM powers up zeroed and MASKS this. Un-zeroed
   `.bss` ⇒ `g_heap_off` trash ⇒ every alloc fails ⇒ only the canary prints
   (exactly 71 bytes) then the core parks in the `_start` wfi loop.
   **Note (2026-07-26): this loader-side zeroing is now redundant-but-kept.**
   The kernels self-zero `.bss` in `_start` (crt0) before any C runs — rv32 `sw`
   loop / rv64 `sd` loop over `[_sbss, _ebss)` in
   `examples/09_embedded/simple_os/arch/riscv{32,64}/boot/baremetal_stubs.c`,
   with `_ebss` padded to `ALIGN(8)` in `common/linker_riscv_common.ld` — so
   the image no longer depends on loader cooperation (board-runnable rule).
   Keep the script step as belt-and-suspenders; verify the crt0 path with
   `GARBAGE_FILL=1 sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs` (the rv32 tb
   never zeroes .bss, so garbage-fill alone exercises the crt0 loop) and
   `GARBAGE_FILL=1 SKIP_BSS_ZERO=1 sh scripts/fpga/ghdl_rv64_k26_ddr_boot.shs`
   (the rv64 tb emulates board step 5b zeroing; `SKIP_BSS_ZERO=1` disables it
   via the tb's `G_SKIP_BSS_ZERO` generic). The tiny BRAM gate gained the same
   knob: `GARBAGE_FILL=1 sh scripts/fpga/ghdl_rv32_tiny_bram_soc.shs` pads the
   `.mem` image with garbage beyond the kernel (loader-side, synthesizable RTL
   untouched).
5. Release the core via the ctrl slave (`0xA000_0000`, magic `0x52563332`
   "RV32"), then poll UART-capture obs regs over JTAG (`hw_server`, NOT openocd)
   and dump the transcript.

### 6b. Tiny-BRAM lane (no DDR, no block design, no FSBL)

A 200 KB-RAM SimpleOS config (`linker_tiny64.ld`, 64 KB stack — measured
high-water is only 344 bytes) + 304 KB ramdisk fits on-fabric:
125.5/144 BRAM36 @ 25 MHz (STARTUPE3 CFGMCLK/2), WNS +20 ns.

```bash
sh scripts/fpga/ghdl_rv32_tiny_bram_soc.shs           # rehearsal (also GARBAGE_FILL=1)
sh scripts/fpga/build_rv32_tiny_bram_bitstream.shs    # bitstream, .mem-initialized BRAM
# program, then read markers via the BSCANE2 USER4 JTAG tunnel:
bash scripts/fpga/read_rv32_tiny_bram_obs.shs transcript > run.log 2>&1
```

**Console transport ("jtagterminal") is configurable.** The readout above is
the cable-free path: the soft-UART bytes are captured on-chip and read back
over the same FT4232H JTAG chain that programs the board — no PMOD wiring at
all. `CONSOLE_MODE=uart` instead points you at the PMOD J2 pins (H12 tx / E10
rx, LVCMOS33, 115200 8N1), which need a **3.3V USB-TTL cable** (never a 5V or
RS-232 one). `BUF_WORDS` must match the bitstream's `UARTBUF_WORDS` generic.

Decoding and the completeness verdict are pure Simple
(`src/lib/hardware/fpga_k26/jtag_console.spl`, spec in `test/`), so the script
now ends with a `COMPLETE:`/`INCOMPLETE:` line and a matching exit code instead
of a hand-compared byte count. The capture buffer is finite (2048 words = 8 KB)
while the core's byte counter keeps running past the end, so an overrun is
reported as `INCOMPLETE ... N bytes LOST` rather than printing a capped prefix
that reads like a whole boot log.

Vivado BRAM landmines: non-pow2 depth pads to the next power of two
(77824 → 131072 words!) — split arrays into ≤3 pow2 banks; shared case-select
writes break BRAM inference (Synth 8-3391); `.mem` INIT needs the elaboration
loop-limit pre-hook. All handled inside the build script.

### 6c. Evidence bar (both lanes)

Persist every run (`> log 2>&1`). A PASS claim needs: IDCODE (`0x04724093`
xck26), program-done marker, and the UART transcript text. Grep verdicts ONLY
from transcript text — binary kernel images contain both `TEST PASSED` and
`TEST FAILED` in their string tables. Compare byte count against the GHDL
baseline (DDR: 446, tiny: 568).

## 6.5 NVMe firmware on the core

The RV32 NVMe controller-policy firmware passes three pre-board GHDL lanes:
behavioral core, exact synthesizable BRAM SoC (clean and `GARBAGE_FILL=1`), and
full AXI4 with wait-state-injected RAM. Run the AXI NAND gate first:

```sh
sh scripts/fpga/ghdl_rv32_nvme_axi_ram.shs
```

It derives `.nandram` from the ELF and proves nonzero AXI reads/writes plus
prevention and recovery. A prior KV260 run recovered all 229 UART bytes through
the tiny-BRAM SoC's USER4 JTAG path, but that is historical evidence until a
fresh source-matched ELF/bitstream/transcript bundle is retained. USER4 is not
host-driven NVMe MMIO.

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

Status 2026-07-26: rv64 passes GHDL on both `rv64_exec_core_flat.vhd` and the
synthesizable `rv64_exec_core_axi.vhd` (incl. GARBAGE_FILL). Silicon: bitstream
built (`soc_top_rv64_k26_ddr.vhd`, timing MET), bring-up via
`bash scripts/fpga/bringup_kv260_rv64_ddr.shs` — same psu_init + `.bss`-zero
flow; kernel loads at DDR `0x1020_0000`. First run: core released but zero AXI
fetches — debug in progress. Note the rv64 top reuses the rv32 ctrl slave, so
`CTRL_MAGIC` reads "RV32" on BOTH bitstreams and cannot identify which is loaded.

## Related

- [kv260_rv64gc_fpga_boot.md](kv260_rv64gc_fpga_boot.md) — KV260 rv64gc bring-up
- [simple_riscv_jtag_debugging.md](simple_riscv_jtag_debugging.md) — JTAG-MMIO readout
- [vivado_device_setup.md](vivado_device_setup.md) — Vivado / hw_server
- `.claude/rules/board-runnable.md` — QEMU is the harness, the board is the target
- RTL: `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core_flat.vhd`,
  `tb_rv32_simpleos_boot.vhd`; runner `scripts/fpga/ghdl_rv32_simpleos_boot.shs`
