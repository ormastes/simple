<!-- codex-architecture -->
# Architecture: StarFive VisionFive 2 NVMe storage

The dependency direction is board provider -> normalized PCI host descriptor -> common PCI enumeration -> common NVMe -> bounded partition lease -> GPT/FAT32/VFS. Common layers never import the StarFive port.

`PciHostDescriptor` describes domain, bounded ECAM buses, outbound windows and DMA policy. `starfive/pcie_host.spl` constructs it only from validated DT resources. A later board-owned preparation capsule handles PHY, clocks, resets, PERST and PLDA quirks, then exposes config access after link validation.

Provisioning is a two-phase capability: read-only identify emits an immutable receipt and challenge; destructive provision accepts only an exact identity-bound challenge and a non-boot, unused namespace. Filesystems receive only a partition-bounded lease, never the raw namespace.

Initial completion mode is polling. MSI is a later StarFive-provider capability and does not change the common NVMe protocol.
