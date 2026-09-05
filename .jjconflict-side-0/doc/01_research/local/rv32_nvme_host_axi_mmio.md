# Local Research: RV32 NVMe Host AXI/MMIO

## Scope

This feature is the missing host-facing transport for the no-alloc RV32 NVMe
firmware. It must let an external AXI host configure the controller, place
64-byte submission queue entries and 16-byte completion queue entries in host
memory, and observe an interrupt. It must reuse the existing NAND-RAM policy;
it must not add a second command implementation.

## Implementation update — 2026-07-28

The missing-transport statements below describe the pre-implementation
baseline. The synthesizable AXI-Lite register/doorbell endpoint, bounded AXI4
queue DMA, firmware mailbox, and interrupt path are now implemented. The
firmware-in-loop GHDL and QEMU parity gates cover Create CQ/SQ, Identify,
Write, Flush, Read, erase/program/read, prevention, retry, refresh, and remap.
KV260 JTAG/MMIO capture tooling also exists. The generated K26 top now has
GHDL boot evidence; Vivado/physical K26 and Cosmos+ NFC/PCIe/NAND acceptance
remain open; see
`doc/08_tracking/feature/rv32_nvme_host_axi_mmio_2026-07-28.md`.

## Existing surfaces

| Surface | Current role | Reusable part | Boundary |
|---|---|---|---|
| `src/os/drivers/nvme/nvme_types.spl` | NVMe opcodes, register offsets, CC/CSTS bits, SQE/CQE sizes | ABI constants | Does not implement an MMIO slave or DMA |
| `src/os/drivers/nvme/nvme_queue_resources.spl` | Bare-metal queue resource validation and doorbell arithmetic | 4 KiB alignment, `4 << DSTRD`, qid doorbells | Does not fetch host queue entries |
| `examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl` | RV32 startup, scalar queue lifecycle, RAM-NAND operations | NAND policy, markers, fixed no-alloc state | Current selftest submits commands internally |
| `examples/.../rtl/rv32_exec_core_axi.vhd` | RV32 CPU AXI4 memory master | CPU memory path | No external IRQ service and no DMA master |
| `examples/.../rtl/rv32_axi4_mem_adapter.vhd` | Single-beat CPU AXI4-to-memory adapter | Generated CPU memory wiring | Cannot represent host queue DMA |
| `examples/.../rtl/rv32_ctrl_obs_slave.vhd` | AXI-Lite debug/control/UART observation | Handshake style only | Not an NVMe register block |
| `examples/.../rtl/soc_top_rv32_k26_ddr.vhd` | CPU plus debug AXI topology | Top-level clock/reset and memory fabric | No NVMe endpoint, DMA, or IRQ route |
| `src/lib/hardware/vhdl_gen/*` | Generator-authoritative RTL sections | Generated-source integration pattern | Must be extended with the endpoint, not bypassed |
| `examples/09_embedded/simpleos_nvme_fw/fw/openssd_config.spl` | Simulator and Cosmos+ profile metadata | Explicit profile selection/fail-closed invalid target | Does not prove PCIe/OpenSSD hardware |

## Current evidence

The existing AXI gate executes the RV32 ELF through the CPU memory adapter and
counts accesses to the linker-resident `.nandram` section. GHDL and KV260 USER4
prove startup, queue lifecycle, erase/program/read, prevention, retry, FCR,
SECDED, and remap markers. That is valid H1 firmware/backend evidence.

It is not host-issued NVMe evidence because the current design has no external
NVMe AXI-Lite register aperture, host queue DMA engine, or external interrupt
path. `rv32_ctrl_obs_slave` is a debug observation slave and must not be
renamed or treated as a BAR/NVMe endpoint.

## Required implementation seam

The smallest complete addition is a synthesizable endpoint with four parts:

1. NVMe register and doorbell AXI-Lite slave with NVMe reset/enable semantics.
2. One bounded queue engine with an AXI4 master for SQE reads and CQE/data
   movement in host DDR.
3. A CPU-visible command/completion mailbox or equivalent fixed scalar ABI so
   the existing firmware service loop owns validation and NAND policy.
4. An external machine-interrupt input, trap entry, and bounded service path.

The endpoint must expose only qid 0 admin and qid 1 I/O initially. Queue depths
are 2 through 16 inclusive. The initial data contract accepts a dword-aligned
PRP1 contained in one page and rejects multi-page PRP2 use. Identify writes
256 bytes; the current NAND data payload is one 4-byte word. This is a deliberate first target, not a
claim of unrestricted NVMe PRP support.

## Research conclusions

- Register offsets and bit meanings must come from the NVMe base ABI already
  represented in `nvme_types.spl`; do not invent Cosmos-specific offsets.
- Doorbell addresses must derive from `CAP.DSTRD` using `4 << DSTRD`.
- Host queue memory is authoritative for the host contract. CPU-local arrays or
  internally generated commands cannot satisfy the gate.
- Completion status must carry CID, SQHD, SQID, phase, and an error status for
  rejected commands.
- Identify, Create CQ, Create SQ, Read, Write, and Flush are the minimum
  end-to-end command set. Unsupported commands and invalid queue/PRP/NSID
  inputs fail closed without media mutation.
- QEMU/RAM-NAND and synthesizable AXI target tests must share the host command
  and completion contract. PCIe enumeration, BAR, MSI, PERST, physical NAND,
  and OpenSSD silicon remain separate H2 gates.

## References

- `doc/08_tracking/feature/rv32_nvme_host_axi_mmio_2026-07-28.md`
- `doc/02_requirements/feature/cosmos_openssd_production_hal.md`
- `doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide.md`
- NVMe Base Specification, NVM Express, official specification index:
  `https://nvmexpress.org/specification/nvm-express-base-specification/`
