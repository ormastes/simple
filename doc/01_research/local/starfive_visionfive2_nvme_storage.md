# Local research: StarFive VisionFive 2 NVMe storage

The repository already has shared PCI enumeration, a pure-Simple NVMe controller/queue implementation, namespace identities, partition leases, FAT32, and VFS block adapters. The current RISC-V PCI path is QEMU-specific (`0x30000000` ECAM), while `NvmeDriver.init_baremetal` accepts an already mapped BAR and uses polling.

The portable seam is a normalized PCI host descriptor consumed by common enumeration. JH7110 DT parsing, PHY/clocks/resets/GPIO/PLDA quirks, link training, and CPU/PCI address translation belong to the StarFive port. NVMe command and filesystem logic must contain no JH7110 constants.

Safety gaps found: partial block writes were zero-padded, lease addition lacked an overflow guard, no production GPT formatter/validator is wired into boot, and the live StarFive entry does not yet enumerate NVMe.

Hardware status on 2026-08-16: Tigard UART/JTAG is enumerated and JTAG previously matched TAP `0x07110cfd`, but the latest UART capture was silent. No NVMe identity or write proof exists yet.

## Linux-aligned implementation update

`src/os/kernel/arch/riscv64/starfive/nvme_probe.spl` now mirrors Linux's ownership boundary: it checks the JH7110 PCIe1 link-status bit at `0x10240368`, uses a bounded 16 MiB ECAM descriptor for domain 1, and scans only for PCI class `01:08:02`. It performs no PCI configuration, BAR, NVMe controller, or media writes. The StarFive image builds through the admitted Stage 3 compiler.

Live execution is currently blocked before image staging because hart 1 remains unexaminable after the earlier failed >4 GiB OpenOCD memory access. The board needs a physical reset/power-cycle; repeated software-reset attempts must not be treated as useful retries.
