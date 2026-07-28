# rv32_nvme_host_axi_mmio_spec

> Runner-backed H1 endpoint contract for RV32 NVMe AXI/MMIO. The GHDL runner
> proves register access, SQE/CQE DMA, mailbox handoff, IRQ, and invalid-CC
> behavior with a testbench-modeled firmware response. It does not prove
> firmware payload/recovery execution or physical transport closure.

| Field | Value |
|---|---|
| Requirements | `doc/02_requirements/feature/rv32_nvme_host_axi_mmio.md` |
| NFRs | `doc/02_requirements/nfr/rv32_nvme_host_axi_mmio.md` |
| Architecture | `doc/04_architecture/rv32_nvme_host_axi_mmio.md` |
| Design | `doc/05_design/rv32_nvme_host_axi_mmio.md` |
| Plan | `doc/03_plan/sys_test/rv32_nvme_host_axi_mmio.md` |
| Source | `test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl` |
| Evidence level | H1 endpoint; firmware response mocked |

## Claim boundary

The endpoint runner issues host NVMe MMIO, fetches a host SQE, exposes it through
the firmware mailbox, DMA-writes a CQE, and checks IRQ/ack behavior. The
testbench supplies the firmware completion. Existing `.nandram` and KV260
internal-selftest runs remain separate NAND policy evidence; neither closes the
firmware-over-endpoint path.

## Scenarios

The executable spec checks:

- NVMe register, CC/CSTS, SQE/CQE, queue alignment, and DSTRD ABI definitions;
- qid 0/qid 1, depth 2..16, one-page PRP1, 256-byte Identify, and 4-byte data limits;
- required MMIO, DMA, IRQ, completion, and NAND evidence obligations;
- explicit simulator, RV32, GHDL, KV260, and Cosmos+ profile boundaries;
- fail-closed handling and the H1 versus H2 claim boundary.

Run with the self-hosted Simple runtime:

```sh
bin/simple test test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl --mode=interpreter
```

Firmware transport closure is a separate gate. It must run the same host command
sequence against QEMU/RAM-NAND and synthesizable GHDL AXI, then require actual
MMIO reads/writes, SQE fetches, CQE writes, payload DMA, IRQ transitions,
completion consumption, and prevention/retry/FCR/remap markers. Missing
transport evidence must not pass through this endpoint-only gate.
