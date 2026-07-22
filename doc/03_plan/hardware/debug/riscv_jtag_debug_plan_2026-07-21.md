# RISC-V JTAG Debug Implementation Plan (2026-07-21)

**Bug**: DEBUG-001 - No CPU-side JTAG TAP/DTM/DMI/Debug Module  
**Status**: PLANNED - Multi-stage implementation  
**Priority**: P1 (deferred until BRAM work lands)

---

## Current State

**Present (host-side)**:
- JTAG cable scripts: `scripts/fpga/*jtag*.shs`
- OpenOCD/T32 probe code: `src/os/realtime/jtag/*.spl`
- FPGA programming helpers

**Absent (CPU-side)**:
- JTAG TAP controller (IDCODE/BYPASS/DTMCS instructions)
- RISC-V Debug Transport Module (DTM)
- Debug Module Interface (DMI) bus protocol
- Debug Module (dmactive, hart select, halt/resume state machine)
- Debug Mode CSRs (dpc, dcsr, dscratch0/1)
- Abstract command execution (GPR read/write)
- System Bus Access (memory access mechanism)
- OpenOCD RISC-V config

---

## Scope: Minimal Ratted RISC-V Debug Subset (v0.13)

Target implementation implements **RISC-V Debug Specification v0.13** minimal ratified subset:

1. **JTAG TAP**: IDCODE, BYPASS, DTMCS instructions
2. **DTM (Debug Transport Module)**: 
   - DTMCS register (version, abits, stat)
   - DMI access protocol (read/write, error detection)
3. **DMI (Debug Module Interface)**:
   - 7-bit address, 32-bit data transfer
   - Error detection (busy, op, exception)
4. **Debug Module**:
   - `dmactive` control bit
   - Single-hart selection (`hartsel`)
   - Halt/resume state machine
   - Status flags: `halted`, `running`, `resumeack`, `havereset`
   - Halt-on-reset support
5. **Abstract Commands**:
   - GPR read/write (x0-x31)
   - Access register command (aarsize, postexec)
6. **Debug Mode CSRs**:
   - `dpc` (Debug Program Counter)
   - `dcsr` (Debug Control & Status: ebreak, cause, step, prv)
7. **Memory Access**: One compliant mechanism (System Bus Access or abstract memory)
8. **OpenOCD Integration**: Config + target definition

---

## Implementation Stages

### Stage 1: TAP + DTM + DMI (Foundation)

**Files to create**:
- `src/lib/hardware/debug/jtag_tap.vhd` - JTAG TAP controller
- `src/lib/hardware/debug/riscv_dtm.vhd` - Debug Transport Module
- `src/lib/hardware/debug/dmi_bus.vhd` - DMI bus interface

**Deliverables**:
- JTAG TAP state machine (Test-Logic-Reset → Run-Test/Idle → Select-DR-Scan → Capture-DR → Shift-DR → Exit1-DR → Pause-DR → Exit2-DR → Update-DR)
- IDCODE register (manufacturer, part number, version)
- DTMCS register (version=1, abits=7, stat=0)
- DMI read/write protocol (address, data, error detection)

**Verification**:
- GHDL testbench simulates JTAG instruction scan
- IDCODE returns expected manufacturer ID
- DTMCS reports correct abits
- DMI read/write completes without error

**Estimated effort**: 5-7 days

---

### Stage 2: Debug Module Core (Halt/Resume)

**Files to create**:
- `src/lib/hardware/debug/riscv_debug_module.vhd` - Debug Module state machine
- `src/lib/hardware/debug/debug_registers.vhd` - DMCONTROL, DMSTATUS, ABSTRACTCS, etc.

**Deliverables**:
- `dmactive` bit (enables/disables debug module)
- `hartsel` register (single-hart select for RV32/RV64)
- Halt request/acknowledge protocol
- Resume request/acknowledge protocol
- Status flags: `halted`, `running`, `resumeack`, `havereset`
- Halt-on-reset configuration

**Hart Interface (deferred until BRAM work lands)**:
```
NOTE: Hart-side integration is DEFERRED to avoid clobbering concurrent opus agent work
on rv32_exec_core.vhd BRAM fixes. Stage 2 implements only the external-facing
Debug Module interface; core-side wiring (haltreq, resumereq, debug mode entry,
trigger escalation) will be added after BRAM work is confirmed stable.

Current stub interface:
- haltreq_o: out std_logic  -- to core halt request
- resumereq_o: out std_logic  -- to core resume request  
- halted_i: in std_logic  -- from core halted status
- running_i: in std_logic  -- from core running status
```

**Verification**:
- GHDL testbench simulates halt/resume cycles
- `dmactive=0` disables all DM operations
- Halt request → `halted=1` within 100 cycles
- Resume request → `running=1` with `resumeack=1`
- Reset triggers halt if halt-on-reset enabled

**Estimated effort**: 7-10 days

---

### Stage 3: Abstract Commands + GPR Access

**Files to create**:
- `src/lib/hardware/debug/abstract_command.vhd` - Command execution engine
- `src/lib/hardware/debug/gpr_access.vhd` - GPR read/write datapath

**Deliverables**:
- Abstract command decoder (register access)
- `abstractcs` register (cmdtype, busy, cmderr)
- GPR read/write (x0-x31, aarsize=2 for 32-bit)
- `data0`/`data1` registers (argument/result transfer)
- Post-execution trigger (`postexec`)
- Error detection (unsupported command, exception)

**Verification**:
- GHDL testbench simulates GPR read/write commands
- Write x5=0xDEADBEEF → read x5 returns 0xDEADBEEF
- x0 access is ignored (hardwired zero)
- Unsupported command → `cmderr=3` (exception)

**Estimated effort**: 5-7 days

---

### Stage 4: Debug Mode CSRs (dpc/dcsr)

**Files to create**:
- `src/lib/hardware/debug/debug_csrs.vhd` - Debug Mode CSR file

**Deliverables**:
- `dpc` register (save/restore PC on debug entry)
- `dcsr` register:
  - `ebreakm/s/u` (ebreak behavior)
  - `cause` (why debug was entered)
  - `step` (single-step enable)
  - `prv` (previous privilege)
  - `mprven` (previous privilege enable)
- CSR save/restore on halt/resume

**Verification**:
- Halt saves current PC to dpc
- Resume loads PC from dpc
- dcsr.cause reports correct halt reason
- Single-step executes one instruction

**Estimated effort**: 3-5 days

---

### Stage 5: Memory Access + OpenOCD Integration

**Files to create**:
- `src/lib/hardware/debug/system_bus_access.vhd` - Memory access mechanism
- `scripts/fpga/openocd_riscv.cfg` - OpenOCD configuration

**Deliverables**:
- System Bus Access module (abstract memory reads/writes)
- Address translation (physical address → bus)
- OpenOCD config:
  - `adapter driver ftdi`
  - `transport select jtag`
  - `target riscv` chain configuration
  - DTM/DMI address mapping
- GDB integration test suite

**Verification**:
- OpenOCD connects to JTAG chain
- `riscv examine_chain` detects TAP/DTM/DM
- GDB `halt`/`continue`/`step` commands work
- GPR read/write via GDB (`info registers`, `set $x5=0x123`)
- Memory read/write via GDB (`x/10 0x8000`)

**STATUS: LANDED `eb2f1734655` (2026-07-22).** Live gdb-multiarch 15.1 session
over OpenOCD 0.12.0 bitbang + GHDL sim, reviewer-reproduced `GDB_E2E: ALL PASS`:
native RSP attach, `info registers`, GPR write + readback, SBA memory
read/write, dpc write, `continue` + Ctrl-C halt, clean detach. `step` is
`monitor step` (dcsr.step via qRcmd), honestly labeled: native `stepi` is
impossible against the tb fake hart (GDB riscv-tdep plants a software
breakpoint at next-pc, which a non-fetching fake hart never hits; GDB's insn
probe also issues 16-bit reads the 32/64-bit SBA rejects). Both limits
dissolve at hart integration. Files: `src/lib/hardware/debug/gdb_e2e.gdb`,
`run_gdb_e2e.shs`, `gdb_e2e.md` (full transcript).

---

## Hart Integration (Deferred - Post-BRAM)

**After BRAM work is confirmed stable**, integrate Debug Module into cores:

**Files to modify** (when safe):
- `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd` - Add debug mode entry
- `examples/09_embedded/fpga_riscv/rtl/rv64_exec_core.vhd` - Add debug mode entry

**Core-side changes**:
- Sample `haltreq` signal → enter Debug Mode
- Flush pipeline → save PC to `dpc`
- Save privilege to `dcsr.prv`
- Set `dcsr.cause` = halt reason
- Implement `resumereq` → restore PC from `dpc`
- Implement single-step (`dcsr.step`)
- Execute abstract commands while halted

**Timing constraint**: Resume core-side integration only after concurrent opus agent confirms BRAM work is stable and no longer editing `rv32_exec_core.vhd`.

---

## Acceptance Criteria

**Simulation (GHDL)**:
- TAP scans IDCODE/DTMCS/BYPASS correctly
- DMI read/write succeeds without errors
- Debug Module halts/resumes hart
- Abstract commands read/write GPRs
- dpc/dcsr save/restore correctly

**Hardware (FPGA)**:
- OpenOCD connects: `openocd -f openocd_riscv.cfg`
- GDB attaches: `target remote localhost:3333`
- Run-control: `halt`/`continue`/`step` work
- GPR access: `info registers`/`set $x5=0x123`
- Memory access: `x/10 0x8000`/`set {int}0x8000=42`

**Regression guard**: Existing RV32/RV64 tests still pass (no performance impact from debug module insertion).

---

## Dependencies & Risks

**Dependencies**:
- BRAM stability (for hart integration)
- No concurrent edits to cores during Stage 2-5
- OpenOCD >= 0.11 (RISC-V support)
- GHDL >= 1.0 (simulation verification)

**Risks**:
- JTAG routing congestion on FPGA (may need floorplanning)
- Debug module timing closure (critical path through halt detection)
- OpenOCD version incompatibilities
- RISC-V Debug Spec interpretation ambiguities

**Mitigation**:
- Keep debug module strictly synchronous (no async paths)
- Use pipelined DMI bus if timing fails
- Start with OpenOCD 0.12 (latest stable)
- Reference Spike/WhisperYart for implementation guidance

---

## Total Estimate

**Stage 1 (TAP/DTM/DMI)**: 5-7 days  
**Stage 2 (Debug Module)**: 7-10 days  
**Stage 3 (Abstract Commands)**: 5-7 days  
**Stage 4 (Debug CSRs)**: 3-5 days  
**Stage 5 (Memory Access + OpenOCD)**: 7-10 days  
**Hart Integration (deferred)**: 5-7 days

**Total**: 32-46 days (≈ 6-9 weeks)

---

## Next Steps

1. ✅ File this implementation plan
2. ✅ **Stage 1 LANDED 2026-07-22** (`e0d8fb67e58`) — `src/lib/hardware/debug/`
   `jtag_tap.vhd` (16-state IEEE 1149.1 TAP, 5-bit IR, IDCODE=0x15350067) +
   `riscv_dtm.vhd` (v0.13 DTMCS version=1 abits=7, sticky dmistat, 41-bit DMI
   scan) + `dmi_bus.vhd` (sync req/resp, 8×32 regfile) +
   `tb_jtag_dtm_dmi.vhd`. GHDL 5/5 PASS (TLR-in-5, IDCODE, DTMCS=0x1071, DMI
   round-trip resp=success, BYPASS), independently re-run by reviewer, exit 0.
   Known simplifications (documented in-file): update-on-rising-TCK (TDO
   registered on falling edge, pin-visible behavior conforms), all TCK-domain
   (no CDC yet — needed at hart integration).
3. ✅ **Stage 2 LANDED 2026-07-22** — `riscv_debug_module.vhd` (DM top,
   resume-handshake FSM, stub hart ports haltreq_o/resumereq_o/ndmreset_o/
   halted_i/running_i) + `debug_registers.vhd` (DMCONTROL/DMSTATUS/HARTINFO/
   ABSTRACTCS/COMMAND) + `tb_debug_module.vhd` (6 checks incl. Stage-1
   regression); `dmi_bus.vhd` routes 0x10–0x1F to DM (scratch 0x00–0x07
   unchanged, defaulted dm_* ports keep Stage-1 tb source-compatible).
   GHDL: STAGE2 PASS + STAGE1 PASS, both exit 0, independently re-run by
   reviewer. v0.13 decisions documented in-file (single hart: hartsel reads
   0; W-only haltreq/resumereq; activation write doesn't honor same-write
   fields; cmderr=2 sticky W1C; version=2/authenticated=1 always readable).
4. ✅ **Stage 3 LANDED 2026-07-22** — abstract commands: DATA0/DATA1,
   COMMAND access-register engine (aarsize 2/3, GPR regno 0x1000–0x101F),
   ABSTRACTCS datacount=2/busy/cmderr {1=busy-violation, 2=not-supported,
   4=not-halted; sticky W1C}, level-held GPR port with ack handshake
   (`tb_abstract_cmds.vhd` 7/7 + Stage-2 + Stage-1 regressions all PASS,
   reviewer re-ran, exit 0). Deviation recorded: tb_debug_module CHECK5
   updated (cmderr 2→4) — that command became valid in Stage 3 and the
   Stage-2 source marked the behavior TBD. Known scoping: dmi_bus forwards
   only 0x10–0x1F, so the tb drives the DM's DMI port directly; DATA0/1
   unreachable through dmi_bus until the scratch collision is resolved
   (Stage-4 prerequisite #1).
5. ✅ **Stage 4 LANDED 2026-07-22** — dmi_bus forwards 0x04–0x0B + 0x10–0x1F
   (scratch shrunk to 0x00–0x03); CSR regno decode with dpc 0x7B1 (halt-pc
   capture, resume-at-dpc, aarsize 2/3) + dcsr 0x7B0 (xdebugver=4, cause
   1/3/4 priority ebreak>haltreq>step, step→step_o with step_pending armed
   on resumereq, prv WARL 0/1/3); other CSRs cmderr=2.
   `tb_debug_csrs.vhd` 6/6 (incl. resume-at-dpc + exactly-one-instruction
   step) and Stage-3 tb re-pointed through the REAL dmi_bus (direct-drive
   dropped — DATA0/1 now proven through the bus); all 4 tbs PASS exit 0,
   reviewer re-ran. tb bring-up finding recorded: poll latched allresumeack
   before allhalted after a step-resume (2-cycle running window race).
6. ✅ **Stage 5 LANDED 2026-07-22 — LIVE OpenOCD ATTACH PASSED.** Full SBA
   engine (SBCS sbversion=1/sbaccess 2/3/readonaddr/readondata/
   autoincrement/sberror+sbbusyerror W1C, SBADDRESS0/1, SBDATA0/1, sb_*
   master port, sba_test_mem target), DTMCS busy/dmireset semantics
   exercised (STAGE1 tb CHECK6), examine-critical DM stub CSRs (misa RO
   RV64IMA, mstatus RW, tselect/tdata1=0). `tb_sba` 6/6 → JTAG STAGE5 PASS
   + all 4 prior stages regression PASS, reviewer re-ran all 5.
   **Real OpenOCD 0.12.0 attached** to the GHDL-simulated stack via
   remote_bitbang (VHPIDIRECT TCP glue, `openocd_bitbang_glue.c` +
   `tb_openocd_bitbang.vhd`): TAP found 0x15350067, hart examined
   (XLEN=64, misa RV64IMA), SBA memory read (`mdd`) + write round-trip
   (`mww`/`mdw` 0xfeedc0de), halt/step (+4)/resume/shutdown rc=0 —
   transcript in `openocd_attach.md`, cfg in `openocd_riscv_sim.cfg`.
7. **Only remaining plan item: hart integration** (gated on BRAM stability):
   wire haltreq/resumereq/halted/running + GPR ack port + pc/prv/ebreak/
   dpc/step into the real rv32/rv64 cores (replace tb fake hart), replace DM
   stub CSRs with the real hart CSR file, connect sb_* to the real SoC bus
   (arbitration vs core), then GDB-over-OpenOCD end-to-end on :3333.
