# Hardware-Required Distinctive Features Completion Plan

**Date:** 2026-04-04  
**Status:** Research-backed execution plan  
**Scope:** Distinctive-feature closure tasks that require **real hardware, probes, or board access**

## Purpose

This plan covers the remaining distinctive-feature work that cannot be truthfully closed from the current machine alone because it depends on physical hardware, vendor tooling, or board ownership.

This plan is intentionally separate from the non-hardware closure plan so that:

- repo truth is not blocked on unavailable hardware
- postponed hardware work has exact requirements instead of vague “test on board later”
- each hardware-dependent lane has:
  - board
  - probe/debug path
  - required host software
  - test flow
  - success markers

## External Research Basis

The following current external references were checked while preparing this plan:

- OpenOCD official docs and GDB integration
  - https://openocd.org/pages/documentation.html
  - https://openocd.org/doc/html/
  - https://openocd.org/doc-release/html/GDB-and-OpenOCD.html
- Lauterbach TRACE32 product and remote API docs
  - https://www.lauterbach.com/products/software/trace32-powerview
  - https://support.lauterbach.com/kb/articles/trace32-remote-api
  - https://www2.lauterbach.com/pdf/api_remote_c.pdf
  - https://www2.lauterbach.com/pdf/app_python.pdf
- Lauterbach GTL / simulation-side integration context
  - https://www.lauterbach.com/products/software/debugger-for-simulators-emulators-and-virtual-targets/gtl
- GHDL simulation reference
  - https://ghdl.github.io/ghdl/using/Simulation.html
- Digilent ZedBoard product/support reference
  - https://digilent.com/zedboard-zynq-7000-arm-fpga-soc-development-board/

These sources support the hardware and tooling assumptions below; they do not replace repo-local proof.

## Hardware-Blocked Feature Areas

### 1. OpenOCD hardware-present proof

Current repo truth:

- OpenOCD lane exists and is host-aware
- smoke/spec coverage is green
- current completion still does not claim universal hardware-present proof

What is missing:

- repeatable hardware-present compile/upload/run/result proof on the actual board
- normalized handling for tool present / board absent / permissions blocked

### 2. TRACE32 hardware-present proof

Current repo truth:

- TRACE32 lane exists and is host-aware
- remote API / power / basic T32 execution specs are real
- the feature still remains qualified because not every host/hardware combination is proven from the same machine

What is missing:

- hardware-present workload proof with a board and active TRACE32 session
- reproducible GUI/headless classification where relevant

### 3. FPGA / ZedBoard / JTAG-backed lane

Current repo truth:

- still explicitly postponed / in-progress
- not part of the promoted authoritative lane set

What is missing:

- board selection freeze
- bitstream / image boot contract
- JTAG-driven execution proof

## Lane-by-Lane Hardware Requirements

## A. STM32H7 OpenOCD lane

### Goal

Promote the OpenOCD row from “host-aware and smoke-proven” to “hardware-present workload-proven”.

### Required hardware

- one supported STM32H7 board already used by repo assumptions
- one ST-LINK or equivalent OpenOCD-supported probe
- USB cable and stable host connection

### Required host software

- `openocd`
- `gdb` / `arm-none-eabi-gdb` as required by the lane
- any board-specific flash/introspection utilities already referenced in repo tests

### Required repo proof path

1. compile bounded workload
2. connect probe through OpenOCD
3. upload or flash image
4. run workload
5. collect result through authoritative result channel
6. classify success/failure with normalized lane status

### Tests to add or strengthen

- hardware-present workload execute
- result-channel assertion suite
- negative cases:
  - missing probe
  - board disconnected
  - permission blocked
  - OpenOCD up but target attach fails

### Success marker

- one deterministic workload returns expected result on real hardware

## B. STM32H7 TRACE32 lane

### Goal

Promote the TRACE32 row from “host-aware and smoke-proven” to “hardware-present workload-proven”.

### Required hardware

- one supported STM32H7 target board
- one TRACE32-compatible debug probe/interface
- working power-control setup if the existing repo flow assumes relay-managed power

### Required host software

- TRACE32 PowerView
- TRACE32 remote API components (`t32rem`, Python/C API path as used by repo)
- any required PRACTICE scripts

### Required repo proof path

1. establish TRACE32 session
2. power / connect target
3. upload or attach workload
4. run bounded workload
5. collect result through debugger console / register readback
6. verify deterministic output

### Tests to add or strengthen

- hardware-present workload execution
- capability-negative matrix
- dialog/screenshot features remain optional unless GUI is explicitly required for promotion

### Success marker

- one deterministic workload result collected on real board through the promoted TRACE32 lane

## C. CH32V307 lane

### Goal

Keep CH32 as a hardware-proven host-aware row, not just an adapter row.

### Required hardware

- CH32V307 board
- WCH-Link or supported WCH debug adapter

### Required host software

- `wlink` tooling used by the lane

### Required proof

- compile/upload/run/result on real board
- normalized missing-board vs missing-tool behavior

### Success marker

- register or RAM sentinel result matches expected workload result

## D. ZedBoard / FPGA lane

### Goal

Either:

- promote a real FPGA/JTAG-backed lane with bounded scope

or:

- formally exclude it from the public distinctive-feature closure

### Required hardware

- Digilent ZedBoard (or a consciously chosen replacement board)
- on-board USB-JTAG or supported external JTAG cable
- stable UART / console path if required by the workload

### Required host software

- AMD Vivado tooling or the exact reduced toolchain path the repo will support
- any OpenOCD/TRACE32/JTAG path actually chosen for the repo

### Required design decisions before implementation

1. Is the authoritative proof:
   - JTAG-loaded baremetal image
   - FPGA bitstream + softcore flow
   - PS-side execution on Zynq ARM
2. Is the result channel:
   - UART
   - register readback
   - debugger console
   - memory sentinel
3. Is this lane part of:
   - remote baremetal
   - VHDL/FPGA backend proof
   - SimpleOS bring-up

### Required proof

- full hardware bring-up doc
- one reproducible boot/execute/result scenario
- clear operator checklist

### Success marker

- a documented board-specific bounded workload can be run by another engineer without hidden tribal knowledge

## Hardware Inventory Matrix

| Lane | Board / Target | Probe / Transport | Host software | Current state | Needed for promotion |
|---|---|---|---|---|---|
| `stm32h7_openocd` | STM32H7 board | ST-LINK / OpenOCD-supported probe | `openocd`, `gdb` | host-aware | hardware-present workload proof |
| `stm32h7_trace32` | STM32H7 board | TRACE32 probe/session | TRACE32 PowerView + Remote API | host-aware | hardware-present workload proof |
| `ch32v307_wlink` | CH32V307 board | WCH-Link | `wlink` | host-aware | repeatable board proof |
| `fpga_jtag_zedboard` | ZedBoard | USB-JTAG / chosen JTAG path | Vivado + chosen debug path | in-progress | board contract + proof |

## How To Acquire / Prepare Hardware

### STM32H7 OpenOCD / TRACE32

- Freeze one exact STM32H7 board SKU in the docs
- Freeze one exact wiring/probe setup
- Record required udev/permissions or Windows driver setup
- Record reset/power expectations

### CH32V307

- Freeze one exact WCH-Link revision
- Record expected host OS support
- Record any extra flash/probe permissions

### ZedBoard

- Freeze whether the board uses on-board USB-JTAG only or external cable
- Freeze whether the lane depends on Vivado Hardware Manager, OpenOCD, or TRACE32
- Record UART and power requirements

## Agent Team Breakdown

### Agent A: OpenOCD hardware lane closure
- own board/probe checklist
- own OpenOCD hardware-present spec additions
- own negative capability matrix

### Agent B: TRACE32 hardware lane closure
- own board/probe/session checklist
- own hardware-present workload spec
- own TRACE32 environment automation notes

### Agent C: CH32 hardware lane repeatability
- own CH32 board proof
- own repeated-run stability checks

### Agent D: FPGA/ZedBoard decision and bring-up
- own board selection
- own tooling path decision
- own proof contract draft

### Main agent
- integrate hardware docs
- keep public status honest until proof exists

## Required Hardware-Specific Test List

### OpenOCD

- compile/upload/run/result
- attach failure
- probe missing
- board missing
- permission blocked

### TRACE32

- connect/run/result
- relay/power interaction if used
- remote API failure modes
- missing T32 session

### CH32

- upload/run/result
- repeated-run stability
- tool missing vs board missing

### ZedBoard

- board connection smoke
- JTAG visibility
- image load or boot smoke
- result-channel smoke

## Promotion Rule

A hardware-dependent distinctive feature can only be promoted when:

1. required hardware is named precisely
2. required host software is named precisely
3. one engineer can follow the checklist and reproduce the lane
4. the lane has a hardware-present workload proof
5. negative capability states are normalized

## Final Status Policy

Until the above proof exists:

- OpenOCD / TRACE32 / CH32 remain `implemented with qualifiers`
- ZedBoard / FPGA remains `postponed` or `in_progress`

This is the correct status even if local smoke tests are green, because smoke alone is not the same as reproducible hardware-present proof.
