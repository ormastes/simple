# RV32 NVMe Host AXI/MMIO Feature Request

## Open Requests

### FR-RV32-NVME-AXI-0001 - Accept host-issued NVMe commands over AXI/MMIO

- **Filed-on:** 2026-07-28
- **Target:** RV32 NVMe firmware, QEMU/OpenSSD/KV260 profiles
- **Priority:** P0
- **Status:** Open for physical targets. The synthesizable endpoint H1 gate passes
  host register access, two posted SQE DMA fetches, testbench-modeled firmware
  completions, CQE DMA, IRQ/ack, and invalid-CC handling. Firmware-in-the-loop,
  generated CPU/top-level wiring is implemented and byte-identical to its
  generated output. The resident service ELF now passes host-issued Create
  CQ/SQ, Identify, Write, Flush, and Read with AXI RAM recovery/prevention/remap.
  QEMU now passes the same firmware command and recovery sequence through a
  GDB-driven guest-RAM mailbox. The current endpoint-wired K26 top passes full
  RV32 SimpleOS GHDL boot with zeroed and garbage-filled DDR. Vivado/board
  evidence and physical H2 remain open.
- **Current evidence:**
  `sh scripts/fpga/ghdl_rv32_nvme_host_axi_mmio.shs` reports
  `STATUS: PASS rv32-nvme-host-axi-mmio H1-ENDPOINT firmware=mocked`.
  `sh scripts/fpga/ghdl_rv32_nvme_fw_in_loop.shs` reports
  `STATUS: PASS rv32-nvme-fw-in-loop firmware=real transport=axi-ram` with
  `recovery=1 refresh=2 remap=1 reads=4`.
  `sh scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs` reports
  `STATUS: PASS rv32-nvme-qemu-host-parity firmware=real transport=qemu-gdb-mailbox`
  with the same counters. QEMU does not close AXI/DMA/IRQ evidence.
  `NVME_RV32_SERVICE=1` builds `build/nvme_fw_rv32_service.elf` with the
  verified Stage 3 pure-Simple compiler. Full CLI deployment remains blocked
  by Stage-4 memory growth, not by the former stale-ABI crash.
  `doc/09_report/rv32_k26_endpoint_wired_boot_rehearsal_2026-07-28.md`
  retains the current-top boot result and source/fixture hashes.
- **Requested-semantics:** Add an NVMe register/doorbell and DMA transport that
  lets an external host create admin and I/O queues and submit commands to the
  same firmware controller path. Keep QEMU, RAM-NAND, OpenSSD, and FPGA target
  configuration explicit.
- **Acceptance-criteria:**
  - [x] AXI/MMIO exposes CAP, VS, CC, CSTS, AQA, ASQ, ACQ, and queue doorbells
        with NVMe-spec reset/enable ordering.
  - [x] A host driver creates admin and I/O queues through MMIO and receives
        completions through DMA; internal self-test calls are not accepted.
  - [x] Host-driven erase/program/read reaches the RAM NAND backend and proves
        prevention, retry, FCR, and alternate-slot recovery.
  - [x] The same firmware command/recovery sequence runs against QEMU and the
        synthesizable AXI target.
  - [ ] A physical OpenSSD/KV260 lane retains source-bound MMIO/JTAG/log
        artifacts for the host-issued command sequence.
  - [x] Missing AXI transactions, DMA, interrupts, or host completions fail the
        gate instead of falling back to the internal self-test.
- **Related:** `doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.md`
