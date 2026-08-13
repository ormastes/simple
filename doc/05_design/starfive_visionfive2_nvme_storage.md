# Detail design: StarFive VisionFive 2 NVMe storage

1. Validate preserved DTB PCIe1 `compatible`, `status`, `reg`, `ranges`, `dma-ranges`, and aperture bounds.
2. Prepare/validate JH7110 PCIe1 and train link; normalize resources into `PciHostDescriptor`.
3. Enumerate class `01:08:02`, map a validated BAR0, allocate DMA, and call common polling NVMe initialization.
4. Identify controller/namespace and emit a read-only receipt plus identity-bound challenge.
5. After exact authorization, create partition 1 at LBA 2048, write/validate both GPT copies, format only the bounded partition FAT32 as `SIMPLEOS`, and flush.
6. Mount at `/nvme`, persist a nonce file, flush/unmount/remount/read/hash, then correlate `ls /nvme` output with the command nonce.

All arithmetic checks overflow before addition. Sector writes require exactly one sector. Any reset, link, identify, GPT, FAT, flush, remount, or hash error aborts; no QSPI writes are permitted.

The first hardware slice is deliberately read-only: `starfive_find_nvme_read_only()` validates link and reports domain/BDF/vendor/device/class/BAR values. If link is down, it stops with `starfive-pcie1-link-down`; it does not silently perform Linux's clock/reset/PHY/PERST sequence. Cold initialization is the next board-owned capsule and must follow `pcie-starfive.c` plus `phy-jh7110-pcie.c` before common NVMe initialization is admitted.
