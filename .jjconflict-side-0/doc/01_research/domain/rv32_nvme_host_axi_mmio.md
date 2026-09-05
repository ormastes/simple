# RV32 NVMe Host AXI/MMIO Domain Research

Date: 2026-07-28

## Primary Sources

- NVM Express, *NVM Express Base Specification 2.3*, ratified 2025-08-01:
  https://nvmexpress.org/specification/nvm-express-base-specification/
- NVM Express, *Base NVM Express - Part One*:
  https://nvmexpress.org/base-nvm-express-part-one/
- Existing NAND recovery research:
  `doc/01_research/domain/rv32_nvme_nand_read_level.md`

## Transport Requirements

The current ratified Base Specification keeps commands at 64 bytes and common
completions at 16 bytes. Queue sizes are zero based, with at least two entries.
For a memory-based transport, submission doorbell `y` is at
`0x1000 + (2*y)*(4 << CAP.DSTRD)` and its completion doorbell is the following
stride. The controller must expose `CAP`, `VS`, `CC`, `CSTS`, `AQA`, `ASQ`, and
`ACQ`, validate `CC` queue entry sizes, and transition `CSTS.RDY` only after a
valid enable sequence.

The host owns SQ/CQ memory. A valid test therefore has to observe MMIO
configuration, a DMA read of the host SQE, firmware consumption, a DMA write of
the CQE, phase/CID preservation, and interrupt assertion. An internally created
command or a linker-section RAM access is not host NVMe evidence.

## Scoped Profile

The first RV32 profile uses admin queue 0 and I/O queue 1, depths 2 through 16,
one aligned PRP1 page, no PRP2 chain, 256-byte Identify data, and the current
4-byte RAM-NAND data payload.
Unsupported queue layouts, namespaces, commands, or transfer shapes fail with
an NVMe error completion before media mutation. This is H1 AXI/model evidence;
PCIe enumeration, BAR/MSI/PERST behavior, OpenSSD silicon, and physical NAND
remain separate H2 gates.

## Recovery Boundary

The transport does not implement a second media algorithm. Read, write, erase,
prevention, SECDED, read-level retry, FCR, and remap remain owned by the existing
RAM-NAND firmware path documented in the recovery research. Host-driven I/O must
reach that path so transport tests cannot pass by bypassing recovery policy.
