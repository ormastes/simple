# Domain research: StarFive VisionFive 2 NVMe storage

Mainline Linux DT/bindings and drivers identify the VisionFive 2 M.2 socket as JH7110 PCIe1/domain 1. Its ECAM is `0x9c0000000` (16 MiB), bridge/APB is `0x2c000000`, non-prefetchable memory is `0x38000000` (128 MiB), 64-bit prefetchable memory is `0x980000000` (1 GiB), and PHY1 is `0x10220000`.

The board port must validate the preserved DT, initialize or validate clocks/resets/PHY/PLDA/link, and initially use NVMe polling. The common driver receives normalized ECAM, windows, BAR and DMA resources. Destructive provisioning must be tied to controller/namespace identity, never adapter presence or a password.

Primary references: Linux `jh7110.dtsi`, `starfive,jh7110-pcie.yaml`, `pcie-starfive.c`, `pcie-plda-host.c`, and `phy-jh7110-pcie.c`.

## 2026-08-16 follow-up: obtaining the installed device identity

The current SPI U-Boot 2021.10 image reports `Unknown command` for both `pci` and `nvme`; therefore its DT nodes do not prove that the command/driver was compiled. Web examples such as PCI ID `126f:2263` describe somebody else's SSD and must not be used as this board's identity.

StarFive's current boot guide says U-Boot can load from NVMe, and its 6.0.0 software release supports booting one image from SD/eMMC/NVMe. The reliable diagnostic path is consequently:

1. boot a current StarFive Linux/SDK recovery image from removable SD without writing the NVMe;
2. read `/sys/bus/pci/devices/0001:01:00.0/{vendor,device,class}` and `/sys/class/nvme/nvme0/{model,serial,firmware_rev}`;
3. read namespace identity and geometry using `nvme id-ctrl`, `nvme id-ns`, and `lsblk --bytes`;
4. retain the outputs and hashes as the immutable identify receipt before provisioning.

Linux evidence places the M.2 endpoint behind PCI domain 1 at `0001:01:00.0`; domain 0 is the USB-controller lane. Mainline VisionFive 2 DT enables both `pcie0` and `pcie1`. The official board datasheet specifies one PCIe 2.0 M-key socket.

Direct ECAM display from the old U-Boot is a secondary diagnostic only: its PCIe host may not have been initialized, and a raw access can fault or hang. The Tigard/OpenOCD configuration also failed to read the 36-bit ECAM address, so it is not an identity oracle. A RAM-loaded SimpleOS probe remains valid once its StarFive provider performs/validates host initialization and issues NVMe Identify commands.

An upstream U-Boot VisionFive 2 fix confirms that having the PCI driver in the defconfig was insufficient: PCI was not enumerated at boot until `CONFIG_PCI_INIT_R` and a preboot NVMe scan were added. Therefore the observed missing commands are a firmware-build limitation, not evidence that the installed SSD or PCIe link is absent. Safe firmware diagnostics are limited to `version`, `help pci`, `help nvme`, and `printenv preboot`; never `saveenv`.

JTAG can provide PCI identity only when the debug module reports an SBA width of at least 40 bits and firmware has already initialized the link. NVMe model, serial, firmware revision and namespace geometry require an NVMe Identify admin command with queues and DMA; they cannot be inferred from ECAM. Avoid full PCI configuration dumps because pciutils documents that some devices can crash on them.

Sources:

- StarFive JH7110 Boot Guide, U-Boot: https://doc-en.rvspace.org/VisionFive2/Boot_UG/JH7110_SDK/u_boot.html
- StarFive JH7110 Boot Flow: https://doc-en.rvspace.org/VisionFive2/Boot_UG/JH7110_SDK/boot_flow.html
- StarFive VisionFive 2 Datasheet: https://doc-en.rvspace.org/VisionFive2/PDF/VisionFive2_Datasheet.pdf
- Mainline VisionFive 2 DT: https://github.com/torvalds/linux/blob/master/arch/riscv/boot/dts/starfive/jh7110-starfive-visionfive-2.dtsi
- StarFive software releases: https://github.com/starfive-tech/VisionFive2/releases
- U-Boot VisionFive 2 PCI initialization patch: https://lists.u-boot-project.org/pipermail/u-boot/2023-August/528321.html
- Linux PCI sysfs ABI: https://docs.kernel.org/PCI/sysfs-pci.html
- Official nvme-cli: https://github.com/linux-nvme/nvme-cli
