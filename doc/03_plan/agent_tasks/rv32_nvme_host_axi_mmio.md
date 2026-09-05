# Agent Tasks: RV32 NVMe Host AXI/MMIO

## Shared contract

- Endpoint name: `rv32_nvme_axi`.
- Firmware mailbox: `Rv32NvmeHostCommand` / `Rv32NvmeHostCompletion`.
- Manual flow helpers: `step("Configure NVMe MMIO")`,
  `step("Submit host SQE")`, `step("Consume host CQE")`,
  `step("Check NAND recovery evidence")`.
- Checker names: `check_mmio_registers`, `check_queue_dma`,
  `check_completion`, `check_profile_boundary`.
- Unimplemented transport helpers must fail explicitly with `fail(...)`; no
  silent no-op or selftest substitution.

## Lanes

| Lane | Owner | Work |
|---|---|---|
| A | RTL | Endpoint AXI-Lite registers, doorbells, DMA master, IRQ |
| B | RV32 core/top | External machine IRQ, trap/service mailbox, generated VHDL wiring |
| C | Firmware | Fixed scalar mailbox service reusing NAND policy and command guards |
| D | GHDL | Host-driven MMIO/DMA/IRQ testbench and trace artifact |
| E | QEMU | External GDB mailbox host sequence against the real RV32 ELF; no AXI/IRQ claims |
| F | SSpec/docs | Maintain runner-backed endpoint H1 gate, manual, and evidence boundaries |
| G | Review | Generator truth, fail-closed profiles, H1/H2 claim audit |

Sidecar lanes are `N/A` until the shared names above are frozen. Merge owner
is the feature integrator; final reviewer must be a normal/high-capability
model after sidecar findings are reconciled.

## Merge order

1. Land ABI/design and generator interface.
2. Land endpoint plus core/top wiring.
3. Land firmware mailbox service.
4. Land GHDL host test and retained trace.
5. Land QEMU firmware-command parity with an explicit non-transport label.
6. Land SSpec/manual and run verify.

No lane may claim host-NVMe acceptance from the existing internal NAND selftest.
