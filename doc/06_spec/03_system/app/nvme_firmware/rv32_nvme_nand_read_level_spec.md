# RV32 NVMe NAND Read-Level System Specification

## Traceability

This manual accompanies
`test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl` and covers
REQ-RV32-NAND-001 through REQ-RV32-NAND-007 and NFR-RV32-NAND-001 through
NFR-RV32-NAND-004.

## Scenarios

1. Inspect the pure policy for fixed downward and upward retry ladders, bounded
   error counts, ECC gating, corrected-payload gating, block disturb, and legal
   queue/lifecycle transitions.
2. Execute the shell self-test and require its fail-closed wrapper contract.
3. Execute the ELF through the full AXI4 adapter into wait-state-injected RAM;
   require nonzero accesses inside `.nandram`, prevention, recovery, and final
   firmware markers.
4. Execute the same ELF on the behavioral core and exact synthesizable BRAM SoC
   with clean and garbage-filled RAM.
5. Program KV260, read the USER4 observation tunnel, require a complete transcript
   and every ordered NAND marker, and retain hashes for the ELF, bitstream,
   decoder, and raw log.

## Required evidence

The live state line is
`NAND EVIDENCE D1 U1 F5 C3 T1 M1 Q3 X2 S1 PASS`: one downward recovery, one upward
recovery, five successful refresh/remap operations, three corrected recoveries,
one retirement, one remap, three queue completions, two full-queue rejections,
and one firmware run. Success also
requires `ALL RV32 NVME FW CHECKS PASS` with no firmware failure marker.

## Model boundary

The RV32 image is a deterministic controller-policy model. It does not claim
analog threshold-voltage fidelity or implement the full FTL free-block pool.
Those remain the responsibility of `hardware.nand_emu` and the full firmware
FTL. The recorded USER4 PASS is historical; no current physical PASS exists
until a fresh source-matched ELF/bitstream/transcript bundle is retained. The
host NVMe-over-AXI firmware sequence is proved in GHDL and tracked by
`doc/08_tracking/feature/rv32_nvme_host_axi_mmio_2026-07-28.md`.

## Current gate status

The source-matched Retry 15 Stage 2 build produced an 89,668-byte SECDED/remap
ELF and passed behavioral GHDL, exact-BRAM GHDL with clean and garbage-filled
RAM, and full AXI4 RAM GHDL. The AXI gate observed 847 `.nandram` reads and 461
writes inside the exact 256-byte region. Each synthesizable-BRAM run recovered
a complete 229-byte observation transcript matching its own live UART stream
and every ordered marker.
On 2026-07-29, the corrected LLVM process-runtime ABI compiled the exact
canonical native SSpec through the explicit bootstrap compiler handler. It
passed 5 examples with 0 failures in 3:17.08 at 349,924 KiB peak RSS, including
the self-test, clean/garbage GHDL, and AXI prevention/recovery scenarios. This
is focused compiler diagnostic evidence; final release admission still requires
the pure-Simple tool path and standalone docgen.
The hashes and USER4 result below are historical; current physical PASS requires
a fresh retained source-matched ELF/bitstream/transcript bundle.

- BRAM-linked ELF: `a3c1bd2fe25fb4034797a9aad66ebc72b6daac5bda15e28a60a443f9e69e1823`
- KV260 bitstream: `afbe6d1b19e756430e6863fa36c27920cb09340e25106e3c3721155dba74cfea`
- JTAG decoder: `201bf7622bb55814a96afd38aa21ba8321f0ff2cfe1369bb1a2b8f7e7cb00050`
- Raw transcript: `4a8f0e98129b24ff107d9850a37f3152d637005d3f2c4eac478450fa1b8e9a50`
