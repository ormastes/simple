# RV32 NVMe NAND Read-Level Local Research

**Date:** 2026-07-28

## Existing implementation

- `src/lib/hardware/nand_emu/` implements the host Vt model, configurable read
  reference, retention/read-disturb drift, faults, and scenario tests.
- `examples/09_embedded/simpleos_nvme_fw/fw/fil_nand_emu.spl` adapts that model
  to the FIL API and implements `read_at_vref`.
- `fw_rv32/entry.spl` runs a no-heap scalar firmware self-test on RV32.
- `fw_rv32/entry_smp.spl` and `logic_nand_region_core.spl` implement a RAM
  state/data NAND model, but they store no read level and the SMP image is not
  currently buildable because of the tracked large-module compiler defect.
- `ghdl_rv32_nvme_fw.shs` and `ghdl_rv32_nvme_bram_soc.shs` execute the scalar
  RV32 image on the behavioral core and the exact synthesizable BRAM SoC.
- The BRAM SoC retains UART output and exposes it through the USER4 JTAG
  observation tunnel used by `read_rv32_tiny_bram_obs.shs`.

## Gap at start of work

The buildable single-hart RV32 image verifies isolated arithmetic contracts,
not a stateful NAND lifecycle. It has no reserved RAM media record, read-level
state, read-retry ladder, corrected-read refresh decision, or granular markers
for startup, queue creation, erase, program, read, prevention, and recovery.

## Smallest shared fix

Reserve a bounded `.nandram` region in both RV32 linker layouts. Keep the media
operations in Simple: state, data, threshold level, read count, refresh count,
recovery count, status, and lifecycle stage are volatile words in that region.
Pure helpers decide sensing, retry order, refresh need, and legal transitions.
The RV32 entry drives the same sequence under QEMU, GHDL, and FPGA and emits
stage markers over UART; existing JTAG UART capture supplies hardware evidence.

This does not replace the full host Vt model or claim transistor-level physics.
It is a deterministic controller-policy model that proves changing the read
reference changes the observed data and that firmware responds correctly.

## Implemented resolution

The direct single-hart image now owns a 64-word `.nandram` record, explicit
device/admin/I/O queue lifecycle, bounded SQ/CQ cursors, erase/program/read,
bidirectional ECC-gated read retry, block read-disturb prevention, verified FCR,
and alternate-slot remap telemetry. Full-word SECDED decodes from stored parity
without a hidden-data oracle; failed-primary FCR verifies alternate-slot data
before switching the active mapping. The corrected image passes QEMU,
behavioral GHDL, exact-BRAM GHDL with clean and garbage-filled RAM, and full
AXI4 GHDL. The AXI run remaps `.nandram` `0x80008AB0..0x80008BAF` to RAM at
`0x10008AB0` and observed 847 reads plus 460 writes. The rebuilt image also
passed on KV260 through USER4 JTAG: 229 emitted bytes, 229 recovered, no loss,
`pass_seen=1`, and `fail_seen=0`.
