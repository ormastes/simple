# RV32 NVMe Host AXI/MMIO Feature Request

## Open Requests

### FR-RV32-NVME-AXI-0001 - Accept host-issued NVMe commands over AXI/MMIO

- **Filed-on:** 2026-07-28
- **Target:** RV32 NVMe firmware, QEMU/OpenSSD/KV260 profiles
- **Priority:** P0
- **Status:** Open. The standalone synthesizable endpoint H1 gate now passes
  host register access, two posted SQE DMA fetches, testbench-modeled firmware
  completions, CQE DMA, IRQ/ack, and invalid-CC handling. Firmware-in-the-loop,
  generated CPU/top-level wiring is implemented and byte-identical to its
  generated output. The resident service ELF builds and enters the mailbox
  loop. A full K26 boot rehearsal is waiting for its RV32 kernel fixture, and
  firmware-in-the-loop host-command simulation,
  QEMU parity, Vivado/board evidence, and physical H2 remain open.
- **Current evidence:**
  `sh scripts/fpga/ghdl_rv32_nvme_host_axi_mmio.shs` reports
  `STATUS: PASS rv32-nvme-host-axi-mmio H1-ENDPOINT firmware=mocked`.
  `NVME_RV32_SERVICE=1` builds `build/nvme_fw_rv32_service.elf` with the
  verified Stage 3 pure-Simple compiler. Full CLI deployment remains blocked
  by Stage-4 memory growth, not by the former stale-ABI crash.
- **Requested-semantics:** Add an NVMe register/doorbell and DMA transport that
  lets an external host create admin and I/O queues and submit commands to the
  same firmware controller path. Keep QEMU, RAM-NAND, OpenSSD, and FPGA target
  configuration explicit.
- **Acceptance-criteria:**
  - [ ] AXI/MMIO exposes CAP, VS, CC, CSTS, AQA, ASQ, ACQ, and queue doorbells
        with NVMe-spec reset/enable ordering.
  - [ ] A host driver creates admin and I/O queues through MMIO and receives
        completions through DMA; internal self-test calls are not accepted.
  - [ ] Host-driven erase/program/read reaches the RAM NAND backend and proves
        prevention, retry, FCR, and alternate-slot recovery.
  - [ ] The same SSpec runs against QEMU and the synthesizable AXI target; a
        physical OpenSSD/KV260 lane retains MMIO/JTAG/log artifacts.
  - [ ] Missing AXI transactions, DMA, interrupts, or host completions fail the
        gate instead of falling back to the internal self-test.
- **Related:** `doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.md`
