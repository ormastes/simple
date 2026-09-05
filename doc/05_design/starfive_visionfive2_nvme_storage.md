# Detail design: StarFive VisionFive 2 NVMe storage

1. Operator precondition for physical provisioning: run checker mode
   `--identify-live`. It sends only `nvme identify`, captures exact controller
   and namespace geometry over Tigard UART, binds it to the admitted image, and
   emits an atomic read-only receipt plus an exact SHA-256 confirmation. A Linux
   `lspci`/`nvme id-*` audit is useful corroboration but is not trusted in place
   of the fresh SimpleOS identity receipt.
2. Normalize PCI host inputs by first building a minimal, validated `PciHostDescriptor` from known-good constants for VisionFive 2; then, when firmware-visible DT is present and safe, override only explicit, validated fields (`ecam`, `ranges`, `dma-ranges`, `bus-range`, clocks/resets/PERST references) without introducing StarFive-only constants in shared layers.
3. Initialize host (`pcie_init`) and verify link; if firmware already trained/link-down evidence exists, proceed without reprogramming unsafe PLL/PHY fields. Then probe for class `01:08:02` on expected bus/function; if no endpoint appears, report blocked state.
4. Map one NVMe BAR0 candidate from common PCI flow, allocate DMA, and invoke shared polling NVMe init path; no media writes occur during this step.
5. Perform read-only Identify Controller/Namespace, compute identity receipt, and build exact-match challenge bindings (serial/nsid/lba_count + identify hash + image hash).
6. Provisioning is allowed only when:
   - `starfive_nvme_format_challenge` challenge matches exactly,
   - device is not mounted/in-use by a running FS contract,
   - boot-source ambiguity is rejected,
   - stable identity replay checks pass.
   - the operator supplies both the receipt-bound SHA-256 confirmation and the
     fixed explicit provisioning phrase; neither is a password or credential.
7. After authorization: create partition 1 at LBA 2048, mirror GPT metadata, format only bounded partition as FAT32 `SIMPLEOS`, verify partition/GPT, and flush write cache.
8. Mount at `/nvme` through the VFS adapter, write a nonce proof file, flush, unmount/remount, reread hash, and verify `ls /nvme` includes expected proof artifact as durable success evidence.

The host checker retains separate identify, provision, and correlated `ls`
UART transcripts. Provisioning fails closed if identity changes, a flush or
remount marker is missing, or the proof entry appears outside the fresh
`nvme_ls_begin`/`nvme_ls_end` command window.

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
