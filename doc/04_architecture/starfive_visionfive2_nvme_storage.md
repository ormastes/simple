<!-- codex-architecture -->
# Architecture: StarFive VisionFive 2 NVMe storage

The dependency direction is board provider -> normalized PCI host descriptor -> common PCI enumeration -> common NVMe -> bounded partition lease -> GPT/FAT32/VFS. Common layers never import the StarFive port.

`PciHostDescriptor` describes domain, bounded ECAM buses, outbound windows and DMA policy. `starfive/pcie_host.spl` currently constructs it from reviewed constants, while board ownership remains responsible for PHY, clocks, resets, PERST and PLDA quirks. A follow-up hardening step is to validate these values from preserved DT resources and keep the common driver host-neutral.

Provisioning is a two-phase capability: read-only identify emits an immutable receipt and challenge; destructive provision accepts only an exact identity-bound challenge and a non-boot, unused namespace. Filesystems receive only a partition-bounded lease, never the raw namespace.

Initial completion mode is polling. MSI is a later StarFive-provider capability and does not change the common NVMe protocol.
