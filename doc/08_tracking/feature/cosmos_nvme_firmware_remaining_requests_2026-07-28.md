# Cosmos NVMe Firmware Remaining Requests

## FR-COSMOS-001 - Admit and execute the production SSpec

- **Status:** Requested; blocked by the self-hosted compiler/runtime lane.
- **Priority:** P0.
- **Acceptance:** A source-matched pure-Simple runtime passes the essential
  tooling gate, executes the Cosmos and simulation SSpecs, and generates both
  manuals with zero stubs.

## FR-NVME-FW-TARGETS-0001 - Make firmware target configuration explicit

- **Status:** Implemented profile matrix; QEMU firmware parity passes and unavailable hardware remains fail closed.
- **Priority:** P0.
- **Acceptance:** One target-neutral firmware core selects explicit profiles
  for Simple simulation, QEMU/FEMU, Cosmos+ OpenSSD 2Ch8Way and 8Ch8Way, and
  KV260/FPGA. Every profile declares CPU, transport, media, geometry, MMIO,
  build runner, evidence class, and availability. Unknown or unavailable
  hardware profiles fail closed rather than falling back to simulation.
- **Extension rule:** Additional boards add a profile and evidence adapter;
  they do not fork the NVMe command, FTL, or recovery core.

## FR-COSMOS-002 - Complete production package provenance

- **Status:** Implemented and self-tested; identified-board package execution remains under FR-COSMOS-003.
- **Priority:** P1.
- **Acceptance:** The package manifest binds repository revision and dirty
  state, tool versions, selected profile, board identity, and hashes for FSBL,
  bitstream, firmware ELF, and `boot.bin`; self-tests reject any omission or
  mismatch.

## FR-COSMOS-003 - Execute physical production acceptance

- **Status:** POSTPONED until the identified Cosmos+ board, destructive NAND
  reservation, power fixture, PCIe host, UART/JTAG, and thermal setup exist.
- **Priority:** P0 production gate.
- **Acceptance:** BT-001..BT-006 all PASS with raw evidence and independent
  review. QEMU, UNO Q, and host mocks cannot satisfy this request.

## FR-COSMOS-004 - Run supplementary UNO Q portability checks

- **Status:** POSTPONED until UNO Q USB/ADB and MCU debug access exist.
- **Priority:** P2.
- **Acceptance:** QRB2210 AArch64 runtime checks and STM32U585 build/UART checks
  pass with retained identities. This is portability evidence only and never a
  Cosmos NFC, PCIe, NAND, FSBL, SMP, or endurance PASS.
