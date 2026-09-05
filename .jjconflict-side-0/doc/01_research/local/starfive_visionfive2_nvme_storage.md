# Local research: StarFive VisionFive 2 NVMe storage

The repository already has shared PCI enumeration and a pure-Simple NVMe controller/queue stack with namespace identity, partition leasing, FAT32, and VFS adapters. The current StarFive host seam still uses firmware-aware constants to build a `PciHostDescriptor` (not a parsed DT path yet), while `NvmeDriver.init_baremetal` accepts an already-mapped BAR and uses polling.

The portable seam is a normalized PCI host descriptor consumed by common enumeration. JH7110 DT parsing, PHY/clocks/resets/GPIO/PLDA quirks, link training, and CPU/PCI address translation belong to the StarFive port. NVMe command and filesystem logic must contain no JH7110 constants.

Safety gaps found: provisioning authorization is still incomplete for this objective, and live acceptance still requires immutable evidence (read-only identify receipt, boot-safe authorization checks, and proof of durable filesystem write/remount). Some early notes still reflect earlier pre-proof runs.

## Linux-aligned implementation update

`src/os/kernel/arch/riscv64/starfive/nvme_probe.spl` now mirrors Linux's ownership boundary: it checks the JH7110 PCIe1 link-status bit at `0x10240368`, uses a bounded 16 MiB ECAM descriptor for domain 1, and scans only for PCI class `01:08:02`. It performs no PCI configuration, BAR, NVMe controller, or media writes. The StarFive image builds through the admitted Stage 3 compiler.

Current hardware update (2026-08-20): boot hart 1 still rejects halt, but full
five-hart declaration shows parked harts 2--4 are examinable. A fixed SBI SRST
trampoline on hart 2, resumed at supervisor privilege, returned hart 2 to the
OpenSBI machine-mode window and therefore proved software reset without flash
writes. RAM staging also uses hart 2. The 366,520-byte load completed, but the
100 kHz readback exceeded the old timeout and the TAP became unstable on later
sessions; UART remained silent. Physical NVMe identity and boot remain BLOCKED
until the Tigard signal path/UART wiring is stable again.

The first live SimpleOS probe path now reports only downstream `domain 1 / bus 1` enumeration (class `01:08:02`) and no longer enumerates PCIe1 root bus ECAM directly. Linux also treats PLDA root-port configuration as a board-specific path and leaves only downstream PCI functions exposed here.
