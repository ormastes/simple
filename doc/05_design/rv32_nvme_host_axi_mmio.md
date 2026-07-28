# RV32 NVMe Host AXI/MMIO Detail Design

## Fixed wire ABI

Register offsets are `CAP 0/4`, `VS 8`, `INTMS 0xC`, `INTMC 0x10`, `CC 0x14`,
`CSTS 0x1C`, `AQA 0x24`, `ASQ 0x28/2C`, and `ACQ 0x30/34`. Doorbells begin at
`0x1000 + (index * (4 << DSTRD))`; even indices update SQ tails and odd
indices update CQ heads.

An SQE is 64 bytes: DW0 opcode/CID, DW1 NSID, DW6-7 PRP1, DW8-9 PRP2, and
DW10-15 command words. A CQE is 16 bytes: result, SQHD/SQID, and CID/status
including phase. Little-endian 32-bit AXI beats are used.

## State machines

1. **Disabled:** `RDY=0`; MMIO stores to queue bases and attributes are
   accepted only as configuration.
2. **Configured:** validate AQA, ASQ, ACQ alignment and depth.
3. **Ready:** accept doorbells, fetch SQEs, and expose bounded mailbox work.
4. **Completion:** write payload/CQE, advance phase on wrap, assert IRQ.
5. **Fatal:** set `CFS`, stop DMA, and require disable/reset.

The endpoint tracks scalar head/tail/phase values for qid 0 and qid 1. It
rejects queue wrap ambiguity, full queues, invalid qids, and doorbells outside
the configured depth.

## Command service

The firmware mailbox ABI contains queue id, CID, opcode, NSID, PRP1/PRP2,
LBA, length, and a small fixed payload area. The endpoint validates address
alignment and range before writing the mailbox. The firmware returns status,
result, and payload length. The endpoint does not interpret NAND policy.

Supported commands are Identify, Create CQ, Create SQ, Read, Write, and Flush.
Read/Write use one dword-aligned PRP1 contained in one page and copy the current
4-byte NAND payload. Identify writes 256 bytes. Unsupported commands and invalid fields return an error CQE and
leave media unchanged.

## Verification hooks

The host testbench must count and retain:

- register reads/writes and doorbell indices;
- SQE fetch and CQE write addresses;
- payload DMA reads/writes;
- IRQ assert/ack transitions;
- completion CID/status/phase and queue wrap;
- NAND policy markers and final read-after-write bytes.

The runner-backed SSpec executes the focused endpoint test and the resident RV32
service ELF against one AXI RAM containing firmware, NAND state, queues, CQEs,
and PRP buffers. It retains recovery, prevention, and alternate-remap counters.
The QEMU scenario executes the same Create CQ/SQ, Identify, Write, Flush, fault
injection, recovery Read, and four prevention Reads against the resident ELF.
An external GDB host writes the mailbox and PRP buffers in guest RAM. Its marker
must say `transport=qemu-gdb-mailbox`; only GHDL may close AXI/DMA/IRQ evidence.

## Deliberate first-target limits

No unrestricted PRP lists, multi-page transfers, MSI-X, PCIe enumeration,
physical NAND timing, or OpenSSD silicon behavior is included. These are
separate increments and must not be implied by H1 success.
