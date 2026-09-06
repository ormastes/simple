# Guide B5 — FPGA JTAG: produce the board-origin OpenOCD halt/regs/step transcript

Owner: the physical-board operator (a human or an agent with the KV260 attached).
NOT runnable on a host without the board — do not simulate.

## What the acceptance spec reads

`test/03_system/plan_acceptance/fpga_board_bringup_jtag_10min_plan_spec.spl`,
scenario "JTAG: board-origin OpenOCD halt/regs/step transcript ...", reads ONE
file — `SIMPLE_FPGA_OPENOCD_TRANSCRIPT` if set, else
`build/fpga/evidence/openocd_halt_regs_step.log` — and requires all of:

| substring | where it comes from |
|---|---|
| `tap/device found: 0x15350067` | OpenOCD's TAP discovery line (the KV260 inner TAP IDCODE the plan recorded 2026-07-24) |
| `halted` | OpenOCD `halted due to debug-request` |
| `pc ` | a register dump line (`reg pc` / gdb `info registers`) |
| `step` | the gdb/OpenOCD step command echo |
| `resume` | OpenOCD resume line |
| `KV260` or `xck26` | board identity — write it as the first line yourself if OpenOCD does not print it |

The checkbox is the OPENOCD path specifically (the hw_jtag raw-mode path is
already ticked). The plan's own blocker note says OpenOCD's tunnel framing is
incompatible with the v1 bridge — so this transcript cannot exist until that
interop bug is fixed; the spec stays RED until then, by design.

## Procedure

1. Fix/verify the tunnel-framing interop (see the bug doc referenced from
   `doc/03_plan/hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md`
   § Current blockers).
2. Attach per `src/lib/hardware/debug/openocd_attach.md` (§ 3 onward) against
   the real board, with a `tee` of the full OpenOCD + gdb session to the
   transcript path. Prepend `Board: KV260 (xck26) <serial> <timestamp>`.
3. Run the spec:
   `src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/fpga_board_bringup_jtag_10min_plan_spec.spl`
   → `2 examples, 0 failures`.
4. Copy the transcript into the plan's evidence directory convention
   (`build/fpga/evidence/rv32_<date>/jtag/`) as well; the default path above is
   what the spec reads.

Tick the box at plan line 130 ONLY with
`— verified <spec command> → 2 examples, 0 failures; transcript <path> sha256 <hash>, board <serial>, <date>`.
