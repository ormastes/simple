# RV32 NVMe Host AXI/MMIO Architecture

## Context

The existing RV32 lane executes an internally driven selftest. Its AXI RAM
adapter exposes CPU memory traffic and `.nandram`; the debug AXI-Lite slave
exposes observation registers. Neither is a host NVMe controller endpoint.

## Components

```text
host AXI-Lite MMIO
        |
  NVMe register/doorbell slave ---- IRQ ----> RV32 external machine interrupt
        |                                      |
  queue/DMA engine AXI4 master <----> host DDR |
        |                                      v
  fixed CPU mailbox -----------------> RV32 firmware service loop
                                           |
                                  existing RAM-NAND policy
```

### NVMe endpoint

Add one synthesizable, generator-owned endpoint. It implements the standard
register aperture (`CAP`, `VS`, interrupt mask/clear, `CC`, `CSTS`, `AQA`,
`ASQ`, `ACQ`) and queue doorbells. `CC.EN` transitions are serialized: disable
clears ready, queue base/size validation happens before enable, and invalid
configuration sets a fatal status without issuing DMA.

The endpoint accepts qid 0 admin and qid 1 I/O only, with depth 2..16. Queue
entry widths are fixed at 64-byte SQE and 16-byte CQE. Doorbells derive from
`CAP.DSTRD`; no target-specific hardcoded stride is permitted.

### DMA and mailbox

The endpoint owns a bounded AXI4 master for host queue memory and the single
page data buffer. It fetches a complete SQE before publishing a command to a
fixed CPU-visible mailbox. Firmware validates the decoded command and reports
the result through the mailbox. The endpoint writes the CQE and data only after
the service result is complete, then asserts the interrupt. No firmware array
or internal selftest submission can stand in for host queue memory.

The initial PRP contract accepts dword-aligned PRP1 within one 4 KiB page. It
writes 256 bytes for Identify, while the existing RAM-NAND data payload remains
one 4-byte word. PRP2 and multi-page
requests are rejected with a completion status until a segmented-DMA design is
implemented.

### Firmware service

Extract or share the existing scalar queue/media helpers. The service loop
consumes one mailbox command at a time, validates opcode/NSID/queue/PRP and
dispatches Identify/Create queues/Read/Write/Flush into the existing NAND-RAM
policy. It emits explicit completion status for every rejection. Recovery,
prevention, retry, FCR, SECDED, and remap remain backend policy.

### Interrupt path

Extend the RV32 core variant with an external machine-interrupt input and
bounded trap entry. The top-level connects the endpoint IRQ to that input.
The handler acknowledges the endpoint and services the mailbox; a missing IRQ
or a timeout is a test failure. Existing debug/UART observation remains a
separate slave.

## Ownership and generation

The VHDL generator is authoritative. The endpoint, core IRQ port, top-level
connections, and DMA fabric must be represented in `src/lib/hardware/vhdl_gen`
and regenerated into the FPGA RTL tree. A generator truth check must compare
the generated source with the checked-in target source.

## Profile boundaries

- `TARGET_SIMPLE_SIM` and the existing `fw/` are host-runnable semantic
  baselines, not host AXI hardware.
- `fw_rv32` plus QEMU/GHDL is the H1 no-alloc implementation target.
- KV260 FPGA execution can provide H1 FPGA-model evidence only when the host
  MMIO/DMA/IRQ protocol is exercised and retained.
- Cosmos+ OpenSSD profiles remain explicit vendor/H2 targets. No QEMU or AXI
  model may claim PCIe enumeration, BAR/MSI/PERST, physical NAND, or silicon
  acceptance.

## Failure policy

Unknown profile, malformed queue, invalid address, unsupported command, DMA
timeout, IRQ timeout, or controller fatal state stops the scenario. There is
no fallback to the internal selftest or simulator profile.
