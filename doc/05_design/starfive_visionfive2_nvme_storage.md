# Detail design: StarFive VisionFive 2 NVMe storage

1. Validate preserved DTB PCIe1 `compatible`, `status`, `reg`, `ranges`, `dma-ranges`, and aperture bounds.
2. Prepare/validate JH7110 PCIe1 and train link; normalize resources into `PciHostDescriptor`.
3. Enumerate class `01:08:02`, map a validated BAR0, allocate DMA, and call common polling NVMe initialization.
4. Identify controller/namespace and emit a read-only receipt plus identity-bound challenge.
5. After exact authorization, create partition 1 at LBA 2048, write/validate both GPT copies, format only the bounded partition FAT32 as `SIMPLEOS`, and flush.
6. Mount at `/nvme`, persist a nonce file, flush/unmount/remount/read/hash, then correlate `ls /nvme` output with the command nonce.

All arithmetic checks overflow before addition. Sector writes require exactly one sector. Any reset, link, identify, GPT, FAT, flush, remount, or hash error aborts; no QSPI writes are permitted.

The board-owned `starfive_jh7110_pcie1_initialize()` capsule now mirrors the
mainline Linux PHY/STG/PLDA programming sequence and readback-validates each
masked update. It admits an existing firmware-trained link immediately. On a
down link it requires a responsive PLDA APB aperture as evidence that firmware
left clocks enabled and resets deasserted, programs only documented controller
registers, and bounds link polling to ten 100 ms slots. It deliberately does
not guess clock/reset-controller fields or directly drive GPIO28/PERST; failure
to prove those firmware-owned prerequisites blocks ECAM access. The subsequent
`starfive_find_nvme_read_only()` reports domain/BDF/vendor/device/class/BAR
values without PCI configuration or media writes.
