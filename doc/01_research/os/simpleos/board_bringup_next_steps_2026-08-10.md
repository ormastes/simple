# SimpleOS WM Board Bringup — Research & Next Steps

Date: 2026-08-10
Status: RESEARCH COMPLETE — Ready for board-bringup phase
Rule: `.claude/rules/board-runnable.md`

## Executive Summary

Physical Xilinx ML Carrier Card (KV260/K26, serial `XFL1OSWWFM2B`) is present at `/dev/ttyUSB0-3`. All tooling, RTL source, and automation scripts exist. **The blocking artifact is a missing FPGA bitstream** (`build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit`), which requires one multi-hour Vivado 2025.2 synthesis job. This document consolidates the exact next commands and prerequisites.

## Verified Preconditions

### Hardware Present
- **Device**: Xilinx ML Carrier Card (FT4232H Quad UART/JTAG), serial `XFL1OSWWFM2B`
- **Part**: Kria K26 SOM (xck26-sfvc784-2lv-c), board part `xilinx.com:kv260_som:part0:1.4`
- **USB identity**: `Xilinx_ML_Carrier_Card_XFL1OSWWFM2B` (verified via udevadm 2026-08-10)
- **Device nodes**: `/dev/ttyUSB0`, `/dev/ttyUSB1`, `/dev/ttyUSB2`, `/dev/ttyUSB3` (FT4232H channels A–D)
- **JTAG channel**: Ch.A (`ttyUSB0`) — Vivado hw_server only (proprietary, incompatible with openocd/openFPGALoader)
- **Board present**: Yes (physically reachable and verified)

### Toolchain Installed
- **Vivado**: 2025.2 installed at `$HOME/Xilinx/2025.2/Vivado/settings64.sh` ✓
- **Vivado support**: Zynq UltraScale+ MPSoC family available ✓
- **RISC-V toolchain**: `riscv64-unknown-elf-objcopy`, `riscv64-unknown-elf-nm` or `llvm-nm` (required for bringup binary conversion) ✓
- **Vivado runtime**: `hw_server`, `xsdb` (embedded in Vivado) ✓

### RTL Source & Automation
- **RTL source directory**: `examples/09_embedded/fpga_riscv/rtl/` ✓
- **Key files**:
  - `soc_top_rv32_k26_ddr.vhd` (15.3 KB, top-level design)
  - `rv32_exec_core_axi.vhd` (35.6 KB, soft-core AXI master)
  - `rv32_axi4_mem_adapter.vhd` (8.5 KB, address translation)
  - `rv32_ctrl_obs_slave.vhd` (9.2 KB, JTAG observation interface)
- **Build script**: `scripts/fpga/build_k26_rv32_ddr_bitstream.shs` ✓
- **Bringup script**: `scripts/fpga/bringup_kv260_rv32_ddr.shs` ✓

## Synthesis Prerequisites & Constraints

### Memory and Concurrency Guardrails
- **Required free RAM**: ≥30 GB (script refuses to run otherwise; prevents host OOM)
- **Max concurrent Vivado instances**: Exactly 1 (checked via `pgrep -f '[l]nx64\.o/vivado'`)
- **Max concurrent `simple native-build`**: 0 during Vivado (unless `ALLOW_CONCURRENT_BUILD=1`)
- **Override flags**: `ALLOW_LOW_MEM=1` and `ALLOW_CONCURRENT_BUILD=1` available if host state is known safe

### Design Specifications
- **Design**: RV32 soft-core (Simple RISC-V implementation) + Zynq PS DDR4 interface
- **Memory layout**:
  - Soft-core internal fetch: 0x80000000 (remapped to DDR 0x10000000)
  - Stack: 0x8081d010 (~8.19 MB contiguous)
  - FAT32 ramdisk: 0x88000000 (remapped to DDR 0x18000000)
  - Control/observation slave: PS aperture at 0xA0000000 (16 KB register/UART buffer)
- **Frequency**: Uses PS PL clock 0 (set by automation rule)
- **Fabric UART**: PMOD J2 pin H12 (NOT routed to onboard FT4232H; JTAG is only observation path without external wiring)

### Build Output
- **Expected artifacts**:
  - `build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit` (bitstream, ~4–5 MB)
  - `build/fpga/k26_rv32_ddr/k26_rv32_ddr.xsa` (hardware specification archive, contains `psu_init.tcl`)
  - `build/fpga/k26_rv32_ddr/util_synth.rpt`, `util_routed.rpt` (resource utilization)
  - `build/fpga/k26_rv32_ddr/timing_routed.rpt` (timing analysis)
  - `build/fpga/k26_rv32_ddr/vivado.log`, `vivado.jou` (tool logs)

## Exact Synthesis Command

```bash
# From repository root. Check prerequisites first:
# - >=30 GB free RAM: free -h | awk '/^Mem:/{print $7}'
# - No running Vivado: pgrep -f '[l]nx64\.o/vivado'
# - No native build: pgrep -f '[s]imple .*native-build'

sh scripts/fpga/build_k26_rv32_ddr_bitstream.shs
```

**Expected duration**: 30–60 minutes wall-clock (measured on similar hardware).
**Output on success**: Script prints `SUCCESS: bitstream at build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit` to stdout and `build/fpga/k26_rv32_ddr/vivado.log`.

### Build Flow Internals (for troubleshooting)
1. **Serialization guards** (lines 54–68):
   - Blocks if another Vivado is running (pgrep check)
   - Blocks if `simple native-build` is running (unless `ALLOW_CONCURRENT_BUILD=1`)
   - Refuses if <30 GB RAM available (unless `ALLOW_LOW_MEM=1`)
2. **RTL validation** (lines 70–73): Confirms all 4 `.vhd` files present and non-empty
3. **Vivado batch mode** (lines 87–193): TCL script inline
   - Creates Vivado project in `build/fpga/k26_rv32_ddr/k26_rv32_ddr`
   - Adds RTL sources and block design (Zynq PS + soft-core + SmartConnect)
   - Runs synthesis (jobs=8), then implementation (jobs=8)
   - Checks timing closure (WNS ≥ 0, WHS ≥ 0); exits with code 3 if timing fails
   - Writes bitstream to `$OUT_BIT` if all steps succeed
4. **Exit codes**:
   - 0: Success, bitstream at `build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit`
   - 1: Setup failure (missing settings file or RTL source)
   - 3: Timing not met (negative slack)
   - 4: Bitstream file not created (check vivado.log)
   - 5: Synthesis failed
   - 6: Implementation failed

## Board Bringup Procedure (Once Bitstream Exists)

Once `build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit` is created, the full bring-up sequence is automated:

```bash
# Compile a SimpleOS kernel for RV32
# (if not already present at build/os/simpleos_riscv32_smf_fs.elf)
# and create a FAT32 ramdisk image (if not at build/os/fat32-riscv32.img)
# Then run:

sh scripts/fpga/bringup_kv260_rv32_ddr.shs
```

### Bringup Sequence (automated by TCL, ~5–10 minutes wall-clock)

1. **Prepare payloads** (shell wrapper):
   - Extract kernel binary from ELF (`objcopy -O binary`)
   - Truncate FAT32 image to 1 MB ramdisk
   - Extract `psu_init.tcl` from XSA (hardware config script)
   - Derive `.bss` offsets from ELF symbols (`_sbss`, `_ebss`, `g_heap_off`) for belt-and-suspenders zeroing

2. **JTAG chain setup** (TCL):
   - Start `hw_server` if not running
   - Connect to JTAG chain
   - Report JTAG targets (board identity proof)

3. **Halt ARM cores** (TCL):
   - Target Cortex-A53 #0 and halt execution
   - Reset all A53 cores (0–3) to invalidate L1/L2 caches
   - Prevents cache eviction from corrupting DDR payload

4. **Zynq PS init** (TCL, **mandatory**):
   - Source `psu_init` from XSA to configure PS clocks and AXI-HP/HPM interfaces
   - Without this step, the control slave reads 0x00000000 on every register and the core never fetches from DDR
   - Takes ~1 second

5. **Program bitstream** (TCL):
   - `fpga -file <bitstream>` to program the PL
   - Remove PS-PL isolation (run `psu_ps_pl_isolation_removal` and `psu_ps_pl_reset_config`)

6. **Verify control slave** (TCL):
   - Read magic register at PS address 0xA0000000+0x24
   - Expected value: 0x52563332 (ASCII "RV32")
   - If mismatch: PL not configured or AXI path blocked

7. **Load DDR** (TCL):
   - Write kernel binary to 0x10000000 (soft-core 0x80000000 via adapter)
   - Write ramdisk binary to 0x18000000 (soft-core 0x88000000 via adapter)
   - Verify first word of kernel and a known rodata word (DDR coherency check)
   - Zero `.bss` region (belt-and-suspenders; kernel crt0 also self-zeroes)

8. **Release core and capture transcript** (TCL):
   - Write 0x1 to control register 0xA0000000+0x00 to release soft-core from reset
   - Poll UART byte counter at 0xA0000000+0x04 for up to 60 seconds
   - Read transcript buffer (16 KB at 0xA0000000+0x8000) once count stabilizes
   - Capture PC, instruction, A0, SP, AXI stats at 0xA0000000+0x08–0x20

### Bringup Script Output Format

Script writes `build/fpga/k26_rv32_ddr/bringup/bringup.log` with TCL markers:
- `BOARD_JTAG_CHAIN_BEGIN` / `BOARD_JTAG_CHAIN_END` — board identity proof
- `APU_HALTED`, `A53_*_RESET_CACHES_INVALIDATED` — cache setup proof
- `PSU_INIT_DONE` — PS configured
- `PROGRAM_HW_DEVICES_DONE` — bitstream loaded
- `CTRL_MAGIC=0x52563332` — control slave reachable and configured correctly
- `CTRL_MAGIC_MISMATCH` (exit 1) — PL not working, or AXI path broken
- `DDR_KERNEL_WORD0=0x...`, `DDR_RAMDISK_WORD0=0x...` — payload coherency proof
- `CORE_RELEASED` — soft-core executing
- `UART_BYTE_COUNT=<n>` — bytes captured in transcript
- `TRANSCRIPT_BEGIN` / `TRANSCRIPT_END` — actual UART output from soft-core
- `TEST PASSED` — full success (if expected in kernel)
- `SimpleOS RV32 boot OK` — kernel booted (exit 2 = partial success)

**Exit codes**:
- 0: Reached `TEST PASSED`
- 2: Core booted (boot marker seen) but did not reach `TEST PASSED`
- 3: No OS markers observed (see log for what core did output)

## Partial Verification Without Full Synthesis

### JTAG Chain Probe (no bitstream required)
The board identity can be verified without synthesis:

```bash
# Start hw_server (embedded in Vivado)
. $HOME/Xilinx/2025.2/Vivado/settings64.sh
nohup hw_server -d > /tmp/hw_server.log 2>&1 &
sleep 2

# Probe JTAG chain via xsdb (batch)
cat > /tmp/probe_chain.tcl <<'TCL'
connect
puts [jtag targets]
puts "CHAIN_OK"
disconnect
TCL
xsdb /tmp/probe_chain.tcl
```

**Expected output**: JTAG target list including `xck26_0` (FPGA) and `arm_dap_1` (ARM DAP).
**Evidence value**: Proves board is reachable and JTAG connection works; does NOT prove PL is configurable.

### Idcode Check (minimal hardware verification)
```bash
# TCL JTAG idcode probe
cat > /tmp/idcode.tcl <<'TCL'
connect
foreach target [jtag targets] { puts "TARGET=$target" }
disconnect
TCL
xsdb /tmp/idcode.tcl
```

**Expected output**: Idcode matching Zynq UltraScale+ MPSoC (xck26 family).

These partial probes are useful for ruling out dead serial connections but cannot verify DDR configuration, AXI paths, or soft-core functionality — those require a full synthesis and bringup.

## Timeline & Resource Budget

| Phase | Duration | Resource | Blocker | Evidence |
|-------|----------|----------|---------|----------|
| **Synthesis** | 30–60 min | ≥30 GB RAM, 1x Vivado | None (all prereqs present) | `build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit` |
| **Bringup (automated)** | 5–10 min | Vivado hw_server + xsdb | Bitstream from phase 1 | `build/fpga/k26_rv32_ddr/bringup/bringup.log` + transcript |
| **Evidence capture** | <1 min | Log file only | Phase 2 must complete | Transcript showing kernel boot + `TEST PASSED` or `SimpleOS RV32 boot OK` |

## Next Actionable Step

**TODAY (same session if budget remains):**

1. Check free RAM: `free -h | grep Mem`
2. Confirm no competing builds:
   ```bash
   pgrep -f '[l]nx64\.o/vivado' || echo "no vivado"
   pgrep -f '[s]imple .*native-build' || echo "no native build"
   ```
3. Launch synthesis:
   ```bash
   cd /home/ormastes/dev/pub/simple
   sh scripts/fpga/build_k26_rv32_ddr_bitstream.shs 2>&1 | tee /tmp/k26_build.log
   ```
4. Monitor build.log in real-time for `SYNTH_WNS`, `IMPL_WNS`, `BITSTREAM_WRITTEN`, and timing status.

**AFTER synthesis completes (next session if synthesis takes full hour):**

5. Verify bitstream exists:
   ```bash
   ls -l build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit
   ```
6. Launch bringup (requires SimpleOS kernel and FAT32 ramdisk in build/os/):
   ```bash
   sh scripts/fpga/bringup_kv260_rv32_ddr.shs 2>&1 | tee /tmp/k26_bringup.log
   ```
7. Capture transcript as board-runnable evidence per `.claude/rules/board-runnable.md`:
   - Board identity (JTAG chain output from bringup.log)
   - Serial/JTAG transcript (UART capture from soft-core)
   - Exit code = 0 for full success, 2 for partial boot

## Known Gaps & Caveats

### Existing (Outside This Scope)
- **aarch64 EFI-stub**: Tracked separately in `doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`; NOT relevant to RV32/K26 work.
- **x86_64 SimpleOS WM on physical hardware**: Requires different board/architecture; RV32 board-bringup is orthogonal.

### This Session (Mitigation Recorded)
- **Fabric UART wiring**: PMOD J2 pins 1 (TX/H12), 2 (RX/E10), 5 (GND) NOT wired to onboard FT4232H. JTAG observation via xsdb is the only path without external 3.3V USB-UART adapter. **Does not block this bringup** (control slave transcript is JTAG-native).
- **Bitstream timing**: Vivado 2025.2 may be slower than measured 30–60 min on different hardware. Wall-clock can stretch to 90+ min on loaded hosts.

### Build System Quirks (Already Handled by Scripts)
- PSU init is **mandatory**; skipping it leaves control slave unresponsive and core unable to fetch from DDR.
- A53 cache reset is **mandatory** to prevent coherency failures on silicon (U-Boot runs before script halts cores).
- ELF-derived `.bss` offsets must be computed at runtime; stale hardcoded offsets corrupt the payload.

## References & Further Reading

- **Build script**: `scripts/fpga/build_k26_rv32_ddr_bitstream.shs` (lines 1–205)
- **Bringup script**: `scripts/fpga/bringup_kv260_rv32_ddr.shs` (lines 1–270)
- **Hardware guide**: `doc/07_guide/hardware/fpga/kria_k26_ml_carrier_bringup.md`
- **Bug tracking**: `doc/08_tracking/bug/simpleos_wm_lane_not_board_runnable_2026-08-08.md`
- **Board-runnable rule**: `.claude/rules/board-runnable.md`
- **Vivado docs**: AMD K26 SOM datasheet + Kria boot firmware guide (links in hardware guide)

## Verification Checklist (for landing board-runnable evidence)

- [ ] Bitstream synthesis completes with timing MET
- [ ] Bringup script outputs `BOARD_JTAG_CHAIN_BEGIN` / `END` (board identity)
- [ ] Control slave magic = 0x52563332 (PL + AXI working)
- [ ] DDR payload coherency (word0 and banner word match expected)
- [ ] Core released and executing (`CORE_RELEASED` + `UART_BYTE_COUNT > 0`)
- [ ] Transcript captured and visible in bringup.log
- [ ] Kernel boot marker or `TEST PASSED` in transcript
- [ ] Transcript saved to `doc/09_report/board_evidence/simpleos_rv32_k26_bring_up_transcript_2026-08-10.txt`
- [ ] PR lands with evidence path and git link to commit

---

**Next session should run synthesis step immediately — it is the only remaining pre-execution work.**
