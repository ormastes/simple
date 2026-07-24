# Shared-Link JTAG Debug — Operator Manual

> An operator with only ONE physical cable to the board still needs three things at once: a live firmware log stream, a terminal, and a JTAG debug session for a hung RISC-V hart. This feature multiplexes all of it over that single link (`LinkMux`/`LinkDemux`, COBS-framed, CRC-16 checked) and tunnels standard `remote_bitbang` JTAG bytes on one of the channels. On the FPGA side the bytes drive a real RISC-V Debug Spec v0.13 stack — TAP -> DTM (IDCODE/DTMCS/DMI) -> Debug Module -> the target hart — so the operator can halt the hart, inspect and patch a register, and resume, all while log traffic keeps flowing on the same wire without corrupting the debug session. The FPGA-side transport and Debug Module also exist as a VHDL mirror under `src/lib/hardware/debug/` (`jtag_tap`, `riscv_dtm`, `dmi_bus`, `debug_registers`) so this behavioural `.spl` model and the synthesizable RTL agree register-for-register.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared-Link JTAG Debug — Operator Manual

An operator with only ONE physical cable to the board still needs three things at once: a live firmware log stream, a terminal, and a JTAG debug session for a hung RISC-V hart. This feature multiplexes all of it over that single link (`LinkMux`/`LinkDemux`, COBS-framed, CRC-16 checked) and tunnels standard `remote_bitbang` JTAG bytes on one of the channels. On the FPGA side the bytes drive a real RISC-V Debug Spec v0.13 stack — TAP -> DTM (IDCODE/DTMCS/DMI) -> Debug Module -> the target hart — so the operator can halt the hart, inspect and patch a register, and resume, all while log traffic keeps flowing on the same wire without corrupting the debug session. The FPGA-side transport and Debug Module also exist as a VHDL mirror under `src/lib/hardware/debug/` (`jtag_tap`, `riscv_dtm`, `dmi_bus`, `debug_registers`) so this behavioural `.spl` model and the synthesizable RTL agree register-for-register.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #shared-link-jtag-debug |
| Category | Hardware \| RISC-V Debug |
| Status | Implemented |
| Requirements | doc/03_plan/hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md |
| Plan | doc/03_plan/hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md |
| Design | src/lib/hardware/link_mux/ |
| Research | N/A |
| Source | `test/01_unit/lib/hardware/link_mux/jtag_debug_scenario_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

An operator with only ONE physical cable to the board still needs three things
at once: a live firmware log stream, a terminal, and a JTAG debug session for a
hung RISC-V hart. This feature multiplexes all of it over that single link
(`LinkMux`/`LinkDemux`, COBS-framed, CRC-16 checked) and tunnels standard
`remote_bitbang` JTAG bytes on one of the channels. On the FPGA side the bytes
drive a real RISC-V Debug Spec v0.13 stack — TAP -> DTM (IDCODE/DTMCS/DMI) ->
Debug Module -> the target hart — so the operator can halt the hart, inspect
and patch a register, and resume, all while log traffic keeps flowing on the
same wire without corrupting the debug session. The FPGA-side transport and
Debug Module also exist as a VHDL mirror under `src/lib/hardware/debug/`
(`jtag_tap`, `riscv_dtm`, `dmi_bus`, `debug_registers`) so this behavioural
`.spl` model and the synthesizable RTL agree register-for-register.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Shared link | One physical byte stream carrying LOG, TERM, JTAG, and CTRL channels, fairly interleaved so no channel starves another |
| IDCODE | `0x15350067` — the fixed 32-bit value the DTM shifts out on reset; it identifies the debug transport to the operator's tool |
| DMI | Debug Module Interface — a 41-bit shift register (7-bit address, 32-bit data, 2-bit op) the DTM uses to read/write the Debug Module |
| Abstract command | A DMI `COMMAND` write that reads or writes one GPR (`regno = 0x1000+n`) or the halt-point PC, `dpc` (`regno = 0x7B1`) |
| cmderr | Sticky Debug Module error code (`2` = command not supported) that latches until explicitly cleared |

## Related Specifications

- [`jtag_debug_probe.spl`](../../../../../test/01_unit/lib/hardware/link_mux/jtag_debug_probe.spl) — the runnable, non-SSpec intensive probe this scenario manual is drawn from (gated by `scripts/check/check-riscv-hardware-gates.shs`)

## Scenarios

### Operator debugs a hung RISC-V hart over the shared JTAG/log link

#### attaches over the muxed link, halts the hart, patches a register, and resumes it

- Power on the target: a tiny RISC-V hart executing a known program in RAM
- Reset the TAP over the shared link and read back the DTM's IDCODE
- Confirm the DTM identifies itself with its fixed IDCODE value
   - Expected: idcode equals `DTM_IDCODE`
- Select the DMI instruction so the rest of the session talks to the Debug Module
- Activate the Debug Module (DMCONTROL.dmactive)
- Let the hart run for a couple hundred clock ticks before attaching
- Confirm the hart really is running (its pc has moved on from reset)
- Read DMSTATUS and confirm the Debug Module reports the hart running, not halted
   - Expected: dmstatus_allrunning_bit equals `1`
   - Expected: dmstatus_allhalted_bit_while_running equals `0`
- Request a halt (DMCONTROL.haltreq)
- Read DMSTATUS again and confirm the hart is now halted
   - Expected: dmstatus_allhalted_bit equals `1`
   - Expected: dmstatus_allrunning_bit_while_halted equals `0`
- Read dpc — the program counter the hart was frozen at when it halted
- Confirm dpc matches the pc the hart was actually halted at
   - Expected: dpc equals `halt_pc`
- Inspect GPR x5 — while a burst of firmware log traffic streams concurrently on CH_LOG
- Confirm the concurrent log burst arrived on CH_LOG completely intact
   - Expected: rd_gpr.log_delivered_intact is true
- Confirm x5 holds the value the sample program wrote (`li x5, 42`)
   - Expected: rd_gpr.data & 0xFFFFFFFF equals `GPR_X5_INITIAL_VALUE`
- Patch x5 with a new value (as if fixing up state before resuming)
- Read x5 back to confirm the patch really landed in the Debug Module's model of the hart
   - Expected: rd_gpr_after.data & 0xFFFFFFFF equals `GPR_X5_PATCHED_VALUE`
- Resume the hart (DMCONTROL.resumereq)
- Read DMSTATUS and confirm the resume was acknowledged and the hart is running again
   - Expected: dmstatus_allresumeack_bit equals `1`
   - Expected: dmstatus_allrunning_bit_after_resume equals `1`
- Let the hart execute a few more ticks and confirm it actually continued past the halt point
- Save the DMI transaction transcript as evidence of the completed session
   - Expected: dir_ready is true
   - Expected: write_ok is true
   - Expected: saved equals `transcript`


<details>
<summary>Executable SSpec</summary>

Runnable source: 114 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Power on the target: a tiny RISC-V hart executing a known program in RAM")
val fpga_00_boot = boot_target_hart()

step("Reset the TAP over the shared link and read back the DTM's IDCODE")
val cmds_idcode = append_all(cmds_reset(), cmds_dr_read(32))
val txn_idcode = send_over_shared_link(fpga_00_boot, cmds_idcode, [])
val fpga_01_idcode = txn_idcode.fpga
val idcode = decode_bits(txn_idcode.replies, 32)
val row_idcode = transcript_row("IDCODE", 0, idcode)

step("Confirm the DTM identifies itself with its fixed IDCODE value")
expect(idcode).to_equal(DTM_IDCODE)

step("Select the DMI instruction so the rest of the session talks to the Debug Module")
val fpga_02_dmi_selected = send_over_shared_link(fpga_01_idcode, cmds_shift_ir(IR_DMI), []).fpga

step("Activate the Debug Module (DMCONTROL.dmactive)")
val fpga_03_active = write_dmi_register(fpga_02_dmi_selected, DM_DMCONTROL, DMACTIVE_BIT)

step("Let the hart run for a couple hundred clock ticks before attaching")
val fpga_04_ticked = advance_hart(fpga_03_active, 90)
val fpga_05_running = advance_hart(fpga_04_ticked, 90)
val pc_running = fpga_05_running.hart.soc.core.pc

step("Confirm the hart really is running (its pc has moved on from reset)")
expect(pc_running).to_be_greater_than(RAM_BASE)

step("Read DMSTATUS and confirm the Debug Module reports the hart running, not halted")
val rd_running = read_dmi_register(fpga_05_running, DM_DMSTATUS, [])
val fpga_06_status_read = rd_running.fpga
val row_running = transcript_row("DMSTATUS(running)", DM_DMSTATUS, rd_running.data)
val dmstatus_allrunning_bit = (rd_running.data >> 11) & 1
val dmstatus_allhalted_bit_while_running = (rd_running.data >> 9) & 1
expect(dmstatus_allrunning_bit).to_equal(1)
expect(dmstatus_allhalted_bit_while_running).to_equal(0)

step("Request a halt (DMCONTROL.haltreq)")
val fpga_07_halt_requested = write_dmi_register(fpga_06_status_read, DM_DMCONTROL, HALTREQ_BIT | DMACTIVE_BIT)
val halt_pc = fpga_07_halt_requested.hart.soc.core.pc

step("Read DMSTATUS again and confirm the hart is now halted")
val rd_halted = read_dmi_register(fpga_07_halt_requested, DM_DMSTATUS, [])
val fpga_08_halt_read = rd_halted.fpga
val row_halted = transcript_row("DMSTATUS(halted)", DM_DMSTATUS, rd_halted.data)
val dmstatus_allhalted_bit = (rd_halted.data >> 9) & 1
val dmstatus_allrunning_bit_while_halted = (rd_halted.data >> 11) & 1
expect(dmstatus_allhalted_bit).to_equal(1)
expect(dmstatus_allrunning_bit_while_halted).to_equal(0)

step("Read dpc — the program counter the hart was frozen at when it halted")
val fpga_09_dpc_cmd = write_dmi_register(fpga_08_halt_read, DM_COMMAND, abstract_command_word(false, REGNO_DPC))
val rd_dpc_lo = read_dmi_register(fpga_09_dpc_cmd, DM_DATA0, [])
val fpga_10_dpc_lo = rd_dpc_lo.fpga
val rd_dpc_hi = read_dmi_register(fpga_10_dpc_lo, DM_DATA1, [])
val fpga_11_dpc_hi = rd_dpc_hi.fpga
val dpc = (rd_dpc_lo.data & 0xFFFFFFFF) | ((rd_dpc_hi.data & 0xFFFFFFFF) << 32)
val row_dpc = transcript_row("dpc", REGNO_DPC, dpc)

step("Confirm dpc matches the pc the hart was actually halted at")
expect(dpc).to_equal(halt_pc)

step("Inspect GPR x5 — while a burst of firmware log traffic streams concurrently on CH_LOG")
val log_burst = make_log_burst(40)
val fpga_12_gpr_cmd = write_dmi_register(fpga_11_dpc_hi, DM_COMMAND, abstract_command_word(false, REGNO_GPR_BASE + GPR_X5))
val rd_gpr = read_dmi_register(fpga_12_gpr_cmd, DM_DATA0, log_burst)
val fpga_13_gpr_read = rd_gpr.fpga
val row_gpr_read = transcript_row("GPR x5 (read)", REGNO_GPR_BASE + GPR_X5, rd_gpr.data)

step("Confirm the concurrent log burst arrived on CH_LOG completely intact")
expect(rd_gpr.log_delivered_intact).to_equal(true)

step("Confirm x5 holds the value the sample program wrote (`li x5, 42`)")
expect(rd_gpr.data & 0xFFFFFFFF).to_equal(GPR_X5_INITIAL_VALUE)

step("Patch x5 with a new value (as if fixing up state before resuming)")
val fpga_14_data0_set = write_dmi_register(fpga_13_gpr_read, DM_DATA0, GPR_X5_PATCHED_VALUE)
val fpga_15_data1_set = write_dmi_register(fpga_14_data0_set, DM_DATA1, 0)
val fpga_16_written = write_dmi_register(fpga_15_data1_set, DM_COMMAND, abstract_command_word(true, REGNO_GPR_BASE + GPR_X5))

step("Read x5 back to confirm the patch really landed in the Debug Module's model of the hart")
val fpga_17_readback_cmd = write_dmi_register(fpga_16_written, DM_COMMAND, abstract_command_word(false, REGNO_GPR_BASE + GPR_X5))
val rd_gpr_after = read_dmi_register(fpga_17_readback_cmd, DM_DATA0, [])
val fpga_18_readback = rd_gpr_after.fpga
val row_gpr_patched = transcript_row("GPR x5 (patched)", REGNO_GPR_BASE + GPR_X5, rd_gpr_after.data)
expect(rd_gpr_after.data & 0xFFFFFFFF).to_equal(GPR_X5_PATCHED_VALUE)

step("Resume the hart (DMCONTROL.resumereq)")
val fpga_19_resumed = write_dmi_register(fpga_18_readback, DM_DMCONTROL, RESUMEREQ_BIT | DMACTIVE_BIT)

step("Read DMSTATUS and confirm the resume was acknowledged and the hart is running again")
val rd_resumed = read_dmi_register(fpga_19_resumed, DM_DMSTATUS, [])
val fpga_20_resume_read = rd_resumed.fpga
val row_resumed = transcript_row("DMSTATUS(resumed)", DM_DMSTATUS, rd_resumed.data)
val dmstatus_allresumeack_bit = (rd_resumed.data >> 17) & 1
val dmstatus_allrunning_bit_after_resume = (rd_resumed.data >> 11) & 1
expect(dmstatus_allresumeack_bit).to_equal(1)
expect(dmstatus_allrunning_bit_after_resume).to_equal(1)

step("Let the hart execute a few more ticks and confirm it actually continued past the halt point")
val fpga_21_resumed_ticked = advance_hart(fpga_20_resume_read, 90)
val pc_after = fpga_21_resumed_ticked.hart.soc.core.pc
expect(pc_after).to_be_greater_than(halt_pc)

step("Save the DMI transaction transcript as evidence of the completed session")
val transcript = TRANSCRIPT_HEADER + row_idcode + row_running + row_halted + row_dpc +
    row_gpr_read + row_gpr_patched + row_resumed
val dir_ready = dir_create_all(EVIDENCE_DIR)
expect(dir_ready).to_equal(true)
val write_ok = file_write(EVIDENCE_PATH, transcript)
expect(write_ok).to_equal(true)
val saved = file_read_text(EVIDENCE_PATH)
expect(saved).to_equal(transcript)
expect(saved).to_contain("IDCODE")
expect(saved).to_contain("GPR x5 (patched)")
```

</details>

### Shared-link and Debug Module failure handling

<details>
<summary>Advanced: rejects a frame whose CRC no longer matches its payload, without delivering it</summary>

#### rejects a frame whose CRC no longer matches its payload, without delivering it

- Encode one well-formed JTAG-channel frame
- Corrupt a single payload bit in transit (a cable glitch), leaving framing intact
- Feed the corrupted stream into the FPGA-side demux
- Confirm the bad frame was counted and rejected, not silently delivered
   - Expected: demux_fed.bad_frames equals `1`
   - Expected: demux_peek(demux_fed, CH_JTAG).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode one well-formed JTAG-channel frame")
val payload: [u8] = [0x41.to_u8(), 0x42.to_u8()]
val wire_ok = frame_encode(CH_JTAG, payload)

step("Corrupt a single payload bit in transit (a cable glitch), leaving framing intact")
val corrupt_index = 2      # first payload byte, inside the COBS body (not the length code, not the 0x00 delimiter)
val wire_corrupted = flip_bit(wire_ok, corrupt_index)

step("Feed the corrupted stream into the FPGA-side demux")
val prof = transport_sim_loopback()
val demux_empty = demux_create(prof)
val demux_fed = demux_feed(demux_empty, wire_corrupted)

step("Confirm the bad frame was counted and rejected, not silently delivered")
expect(demux_fed.bad_frames).to_equal(1)
expect(demux_peek(demux_fed, CH_JTAG).len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: reports a command error when the operator asks for a register the Debug Module does not support</summary>

#### reports a command error when the operator asks for a register the Debug Module does not support

- Boot the target hart, reset the TAP, and select the DMI instruction
- Issue an abstract-command read for a regno that is neither a GPR nor dpc
- Read ABSTRACTCS and confirm cmderr reports 'not supported'
   - Expected: cmderr equals `CMDERR_NOT_SUPPORTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the target hart, reset the TAP, and select the DMI instruction")
val fpga_00_boot = boot_target_hart()
val fpga_01_dmi_selected = send_over_shared_link(fpga_00_boot, append_all(cmds_reset(), cmds_shift_ir(IR_DMI)), []).fpga
val fpga_02_active = write_dmi_register(fpga_01_dmi_selected, DM_DMCONTROL, DMACTIVE_BIT)

step("Issue an abstract-command read for a regno that is neither a GPR nor dpc")
val fpga_03_bad_cmd = write_dmi_register(fpga_02_active, DM_COMMAND, abstract_command_word(false, REGNO_UNSUPPORTED))

step("Read ABSTRACTCS and confirm cmderr reports 'not supported'")
val rd_abstractcs = read_dmi_register(fpga_03_bad_cmd, DM_ABSTRACTCS, [])
val cmderr = (rd_abstractcs.data >> 8) & 7
expect(cmderr).to_equal(CMDERR_NOT_SUPPORTED)
```

</details>


</details>

<details>
<summary>Advanced: leaves the Debug Module untouched when a DMI-shaped shift arrives on the wrong TAP instruction</summary>

#### leaves the Debug Module untouched when a DMI-shaped shift arrives on the wrong TAP instruction

- Boot the target hart and reset the TAP, WITHOUT selecting the DMI instruction (reset selects IDCODE)
- Shift a DMI-encoded haltreq write while IDCODE (not DMI) is still selected
- Confirm the hart's halt state is unchanged — the shift was inert without the DMI instruction selected
   - Expected: fpga_01_after_bogus.hart.halted equals `halted_before`
   - Expected: fpga_01_after_bogus.hart.halted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the target hart and reset the TAP, WITHOUT selecting the DMI instruction (reset selects IDCODE)")
val fpga_00_boot = boot_target_hart()
val halted_before = fpga_00_boot.hart.halted

step("Shift a DMI-encoded haltreq write while IDCODE (not DMI) is still selected")
val bogus_halt = dmi_dr_pack(DMI_OP_WRITE, DM_DMCONTROL, HALTREQ_BIT | DMACTIVE_BIT)
val cmds_bogus = append_all(cmds_reset(), cmds_dr_write(bogus_halt, DMI_WIDTH))
val fpga_01_after_bogus = send_over_shared_link(fpga_00_boot, cmds_bogus, []).fpga

step("Confirm the hart's halt state is unchanged — the shift was inert without the DMI instruction selected")
expect(fpga_01_after_bogus.hart.halted).to_equal(halted_before)
expect(fpga_01_after_bogus.hart.halted).to_equal(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md`
- **Plan:** `doc/03_plan/hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md`
- **Design:** `src/lib/hardware/link_mux/`


</details>
