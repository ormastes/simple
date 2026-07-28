# RV32 NVMe Host AXI/MMIO Architecture

## Context

The existing RV32 lane executes an internally driven selftest. Its AXI RAM
adapter exposes CPU memory traffic and `.nandram`; the debug AXI-Lite slave
exposes observation registers. Neither is a host NVMe controller endpoint.

## Components

```text
host AXI-Lite MMIO
        |
  NVMe register/doorbell slave ---- IRQ ----> host/PS interrupt
        |
  queue/DMA engine AXI4 master <----> host DDR
        |
  fixed CPU mailbox <---------------- RV32 firmware polling loop
                                           |
                                  existing RAM-NAND policy
```

### NVMe endpoint

Add one synthesizable endpoint with a pinned hand-owned RTL source. It implements the standard
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

The resident service reuses the existing scalar queue/media helpers. Its loop
consumes one mailbox command at a time, validates opcode/NSID/queue/PRP and
dispatches Identify/Create queues/Read/Write/Flush into the existing NAND-RAM
policy. It emits explicit completion status for every rejection. Recovery,
prevention, retry, FCR, SECDED, and remap remain backend policy.

### Interrupt path

The top-level connects the endpoint IRQ to the ZynqMP `pl_ps_irq0` input so the
host/PS can consume completions. The RV32 firmware polls the fixed mailbox; it
does not need a second interrupt path. A missing host IRQ, acknowledgement, or
mailbox completion is a test failure. Existing debug/UART observation remains
a separate slave.

## Ownership and generation

The VHDL generator is authoritative for the RV32 K26 top and boot testbench.
The dedicated endpoint and firmware-in-loop testbench are hand-owned,
hash-pinned RTL because reproducing state machines and test orchestration as
generated string data adds no independent source of truth. The golden gate
compares generated top/testbench output and separately covers both pinned files.

## Profile boundaries

- `TARGET_SIMPLE_SIM` and the existing `fw/` are host-runnable semantic
  baselines, not host AXI hardware.
- `fw_rv32` plus QEMU/GHDL is the H1 no-alloc implementation target. QEMU
  `virt` has no custom NVMe endpoint: the external GDB host writes the fixed
  mailbox and PRP buffers in guest RAM, proving firmware command/recovery
  parity but not AXI, DMA, or IRQ. GHDL owns those transport claims.
- KV260 FPGA execution can provide H1 FPGA-model evidence only when the host
  MMIO/DMA/IRQ protocol is exercised and retained.
- Cosmos+ OpenSSD profiles remain explicit vendor/H2 targets. No QEMU or AXI
  model may claim PCIe enumeration, BAR/MSI/PERST, physical NAND, or silicon
  acceptance.

## Failure policy

Unknown profile, malformed queue, invalid address, unsupported command, DMA
timeout, IRQ timeout, or controller fatal state stops the scenario. There is
no fallback to the internal selftest or simulator profile.
