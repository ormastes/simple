# rv32_nvme_host_axi_mmio_spec

> Runner-backed H1 contract for RV32 NVMe AXI/MMIO. GHDL proves the endpoint
> protocol both with a focused mailbox model and with the resident RV32 service
> ELF executing host commands and RAM-NAND recovery over shared AXI RAM. QEMU
> separately proves the same firmware command sequence through guest RAM.

| Field | Value |
|---|---|
| Requirements | `doc/02_requirements/feature/rv32_nvme_host_axi_mmio.md` |
| NFRs | `doc/02_requirements/nfr/rv32_nvme_host_axi_mmio.md` |
| Architecture | `doc/04_architecture/rv32_nvme_host_axi_mmio.md` |
| Design | `doc/05_design/rv32_nvme_host_axi_mmio.md` |
| Plan | `doc/03_plan/sys_test/rv32_nvme_host_axi_mmio.md` |
| Source | `test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl` |
| Evidence level | H1 AXI transport plus QEMU firmware-command parity |

## Claim boundary

The aggregate runner retains the focused mocked-mailbox endpoint check, then
boots `nvme_fw_rv32_service.elf` and issues Create CQ/SQ, Identify, Write, Flush,
and Read commands. One shared AXI RAM contains firmware, `.nandram`, queues,
completions, and PRP buffers. The gate injects a retention-level fault and a
primary-verify failure, then requires exact recovered payload, prevention and
recovery refreshes, alternate remap, valid CQ fields, and IRQ acknowledgement.

## Scenarios

The executable spec checks:

- NVMe register, CC/CSTS, SQE/CQE, queue alignment, and DSTRD ABI definitions;
- qid 0/qid 1, depth 2..16, one-page PRP1, 256-byte Identify, and 4-byte data limits;
- required MMIO, DMA, IRQ, completion, and NAND evidence obligations;
- QEMU Create CQ/SQ, Identify, Write, Flush, recovery Read, and prevention Read parity;
- explicit simulator, RV32, GHDL, KV260, and Cosmos+ profile boundaries;
- fail-closed handling and the AXI/QEMU/H2 claim boundary.

Run with the self-hosted Simple runtime:

```sh
bin/simple test test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl --mode=interpreter
```

GHDL firmware transport is closed by
`scripts/fpga/ghdl_rv32_nvme_fw_in_loop.shs`. QEMU firmware parity is closed by
`scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs`; because QEMU `virt` has no custom
endpoint, that runner uses `transport=qemu-gdb-mailbox` and does not prove AXI,
DMA, IRQ, PCIe, or physical-board acceptance.
