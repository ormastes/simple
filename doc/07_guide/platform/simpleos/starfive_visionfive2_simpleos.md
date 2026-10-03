# SimpleOS on StarFive VisionFive 2

This lane targets `riscv64-starfive-jh7110` and enters supervisor mode through
the board's existing OpenSBI/U-Boot firmware. It is a RAM-only bring-up path:
normal tooling must not issue QSPI, eMMC write, erase, NAND, or `saveenv`
commands.

The JH7110 scan chain exposes two TAPs with ID `0x07110cfd`: the E24 monitor
core first and the U74 application complex second. SimpleOS uses U74 hart 1;
targeted OpenOCD operations must select `jh7110.u74_hart1`, not the first TAP.

## Tigard wiring and identity

The admitted adapter is FTDI `0403:6010`, serial `tiBMLHE7`, with EEPROM product
`port A:Serial  port B:JTAG`. Channel A is UART at 115200 8N1; channel B is
JTAG. Scripts resolve stable `/dev/serial/by-id` identities and sysfs interface
metadata, never fixed tty numbers. JH7110 UART0 uses GPIO5 TX and GPIO6 RX;
connect grounds and the Tigard voltage reference to the powered target.
If signal integrity is marginal, set `STARFIVE_JTAG_KHZ` within the validated
1..1000 kHz range. A scan passes only when the log contains two actual
`tap/device found: 0x07110cfd` records and no unexpected-ID or IR-capture error.
The expected ID repeated inside an OpenOCD error message is not evidence. Run
`scripts/os/starfive-jtag-scan.shs --self-test` to verify this oracle.

Run the canonical live workflow with:

```sh
scripts/os/run_simpleos_starfive_jh7110.shs
```

The workflow detects Tigard, builds the admitted ELF and receipt, loads only to
RAM through U-Boot, retains one stateful UART transcript, observes ordered boot
markers, logs into the serial shell, and runs `ls /`. A passing listing is
produced by the mounted VFS and contains `bin`, `etc`, and `README.txt`.

## Failure meaning

- `starfive_status=blocked` with exit 2 means a prerequisite is unavailable:
  adapter ambiguity, UART silence, all-zero/all-one JTAG, or missing admitted
  compiler. It is not PASS.
- Exit 1 means observed failure: wrong TAP (`0x07110cfd` expected), malformed
  evidence, boot failure, forbidden flash vocabulary, or restoration failure.
- PASS requires exact compiler/image/linker hashes, entry/load `0x40200000`,
  validated preserved DTB, ordered entry/console/filesystem/shell markers, real
  `ls /` output, bounded timings, transcript paths, and restored FTDI state from
  the same run.

Current local evidence on 2026-08-16 proves bounded RAM read/write access: the
checker saved the word at `0x48000000`, wrote and read back `0x53464a54`,
restored the original word, resumed U74 hart 1, and rebound Tigard channel B.
The provenance-admitted pure-Simple Stage 3 compiler builds the board ELF. Live
acceptance reaches entry, console, filesystem, and shell markers, and `ls /`
returns `/bin`, `/etc`, and `/README.txt` through the mounted VFS.

JH7110 UART0 is DesignWare 8250-compatible at `0x10000000`, using 32-bit MMIO
accesses and register shift 2. QEMU's byte-wide 16550 provider is not
interchangeable even though its base is identical. A live probe read LSR
`0x60` at `0x10000014` and emitted one byte through a 32-bit THR write. The
StarFive runtime therefore preserves firmware configuration and uses words.

JTAG `load_image` plus `verify_image` proves that ELF segments reached RAM; it
does not prove the OpenSBI/U-Boot handoff. Direct PC resume is diagnostic only.
Production acceptance uses a fresh U-Boot prompt and its reviewed ELF or FIT
handoff so supervisor privilege, hart ID, DTB pointer, and interrupt state are
established together.

After SimpleOS replaces U-Boot, use
`scripts/os/starfive-jtag-sbi-reset.shs` to request an OpenSBI cold reboot. It
writes a three-instruction `ecall` trampoline only to scratch RAM, selects
parked U74 hart 2, sets supervisor resume privilege, invokes SBI SRST, and
restores Tigard channel B. A fresh session must observe hart 2 back in the
OpenSBI machine-mode window. Generic OpenOCD `reset run` is insufficient.
The helper first runs the shared scan-only TAP gate and refuses every halt,
RAM/register write, or resume unless exactly two `0x07110cfd` TAPs are present
with no extra TAP or IR-capture error. The RAM-stage helper enforces the same
gate.

The target configuration declares all five U74 Debug Module harts but does not
join them into an SMP halt group. On the current board boot hart 1 rejects halt
requests while harts 2--4 remain examinable; hart 2 therefore performs RAM
staging and reset injection, while U-Boot on hart 1 owns `bootelf`. A UART
firmware sequence is still required for physical boot PASS. Missing UART or an
unverified `ndmreset` is BLOCKED; do not loop reset attempts.

On the tested U-Boot 2021.10 build, `bootelf -p` faults while processing this
ELF's program headers. `bootelf -s 0x48000000` is the proven loader and reaches
`_start` at `0x40200000`. Because its application ABI supplies argc/argv rather
than OpenSBI's hart/FDT pair, the entry shim validates the preserved FDT magic
at `0x42200000` before binding hart 1. Missing FDT magic remains a hard stop.

## NVMe bring-up

The VisionFive 2 M.2 socket is PCIe1/domain 1. SimpleOS keeps JH7110 DT parsing,
PHY/clocks/resets, PERST, PLDA configuration and link validation in
`src/os/kernel/arch/riscv64/starfive/`; common PCI enumeration and
`src/os/drivers/nvme/` contain no StarFive constants.

Before enumeration, `starfive_jh7110_pcie1_initialize()` admits an already
trained firmware link or restores the register sequence from mainline Linux
`pcie-starfive.c` and `phy-jh7110-pcie.c`: PCIe1 PHY KVCO tuning, root-port
mode, external reference clock and CLKREQ, functions 1--3 disabled, function 0
restored, root-port enable, hidden RC BARs, bridge class, LTR forwarding off,
and 64-bit prefetch support. Every masked write is read back. An inaccessible
PLDA APB aperture is treated as clocks/resets not proven and blocks the scan.
SimpleOS does not guess clock/reset-controller bit positions or drive the
active-low GPIO28 PERST line; those remain part of the preserved U-Boot handoff.
Link training is bounded to ten 100 ms polling slots.

The read-only probe then uses `starfive_find_nvme_read_only()`. It checks link-status
bit 5 at `0x10240368`, scans only downstream bus 1 in the bounded 16 MiB PCIe1 ECAM aperture, and
accepts class `01:08:02`. Its UART line reports domain, BDF, vendor/device IDs,
BARs, and `read_only=1`, or a precise link/not-found reason. It does not write
PCI config, NVMe registers, queues, partitions, or storage.

Do not access domain 1 bus 0 with the ordinary ECAM formula. JH7110's PLDA root
port has a controller-specific root-configuration path; the M.2 endpoint is on
downstream bus 1. An invalid root-bus ECAM access can wedge the U74 hart so that
even the SBI reset trampoline cannot be injected, requiring one physical reset.

Expected admission markers are `STARFIVE pcie1-init-ready
source=firmware-link-ready` or `source=cold-init-link-ready`. Any
`STARFIVE pcie1-init-blocked` marker means ECAM/NVMe access is not authorized;
use its reason rather than retrying an unsafe address.

The vendor U-Boot may report `Unknown command` for `pci` and `nvme`; that is a
firmware configuration limitation, not SSD absence. NVMe model, serial,
firmware and namespace geometry require a real NVMe Identify command with DMA.
Never copy an example device ID from web documentation into an authorization
receipt.

Pre-provisioning Linux check (on the installed VF2 Linux/SDK image):

- `lspci -nn`
- `lspci -nn -s 0001:01:00.0`
- `cat /sys/bus/pci/devices/0001:01:00.0/{vendor,device,class}`
- `nvme list`
- `nvme id-ctrl /dev/nvme0`
- `nvme id-ns /dev/nvme0n1`
- `lsblk --bytes /dev/nvme0`

Save the exact command outputs and use them as the immutable preflight identity
report before running `--provision-live`.

Provisioning is intentionally separate. It requires an immutable identify
receipt bound to exact serial, NSID, capacity and image hash, rejects mounted,
in-use and boot-source devices, creates a bounded GPT partition, formats that
partition as FAT32, and mounts it at `/nvme`. PASS then requires a nonce file to
survive flush, unmount and remount with an equal hash, followed by a command-
correlated public-VFS `ls /nvme`. A password is privilege input, never storage
identity confirmation.

Use `scripts/check/check-starfive-nvme-storage.shs` as the storage acceptance
gate. `--contract` and `--self-test` are host-only safety checks.
`--identify-live` may perform only PCI/NVMe reads and must emit an immutable
Identify Controller/Namespace receipt before it can pass. `--provision-live`
is a separately authorized mode; authorization for it never carries over from
identify or general board boot. The board image now contains the real polling
Identify path, identity-bound UART format command, mirrored GPT writer,
partition-bounded FAT32 formatter, durable remount/readback proof, and public
VFS `/nvme` listing. It also synchronizes non-coherent SQ/CQ, Identify, and
bounce-buffer DMA using retained allocation handles. Live checker promotion is
still blocked until the exact SSD and UART transcript prove those paths. Do not
interpret the PCI identity line or a contract PASS as proof of an NVMe model,
namespace, filesystem, or durable write.

## SD-card NVFS root (riscv64 NVFS-root lane)

**Status: UNVERIFIED ON HARDWARE.** The kernel, drivers and SD image exist and
are proven under QEMU `virt` plus host-side specs; no VisionFive 2 transcript
exists yet (open: `doc/08_tracking/bug/simpleos_riscv64_nvfs_root_board_blocked_2026-10-03.md`).
Unlike the RAM-only lane above, this lane boots from a micro-SD card and its
kernel writes ONLY to the NVFS partition of that card (it never writes a
device without an NVFS superblock; eMMC fails SD identification and is skipped).

The image is the same kernel the QEMU gate boots. It selects everything from
the device tree U-Boot hands it: the console UART from `/chosen stdout-path`
(VF2: alias `serial0` -> `snps,dw-apb-uart@0x10000000`, 32-bit access,
reg-shift 2, LSR at `0x10000014`; U-Boot's 115200 8N1 setup is kept) and the
root device from the DW MSHC nodes (`mmc@16020000` = micro-SD slot), driven
by the pure-Simple PIO driver `src/os/drivers/storage/dw_mshc_sd.spl`. NVFS is
found on SD partition 2 through `src/os/drivers/storage/mbr_window.spl`; there
is no fallback filesystem.

Load address: `boot.scr` loads `Image` to `0x80200000` and `booti`s it in
place. JH7110 DRAM starts at `0x40000000`, so every DRAM size (2/4/8 GiB) covers
`0x80200000..0xA0000000` (kernel, 8 MiB stack, 64 MiB heap, virtio DMA window
`0x90000000` unused on the board); OpenSBI sits at `0x40000000` and U-Boot
relocates itself and its DTB to the top of DRAM, clear of that range.

### Build and write the card (host)

```sh
cargo build --release --bin simple            # in src/compiler_rust (seed)
sh scripts/check/check-simpleos-riscv64-nvfs-qemu.shs   # builds + QEMU-proves the image
# -> build/verify/simpleos-riscv64-nvfs/sdcard.img (MBR: p1 FAT32 Image+boot.scr, p2 0xda NVFS)
lsblk -o NAME,SIZE,MODEL,TRAN                   # identify the card reader: /dev/sdX
sudo dd if=build/verify/simpleos-riscv64-nvfs/sdcard.img of=/dev/sdX bs=4M conv=fsync status=progress
```

To rebuild only the card from an existing kernel/NVFS image:
`sh scripts/os/build-simpleos-riscv64-sdcard.shs --image <Image> --nvfs <nvfs-root.img> --out sdcard.img`.
If the board's U-Boot control DTB does not describe the SD controller as
`starfive,jh7110-mmc`, `starfive,jh7110-sdio` or `snps,dw-mshc`, add
`--board-dtb <jh7110-starfive-visionfive-2-v1.3b.dtb>`; `boot.scr` then passes
`/board.dtb` (loaded to `${fdt_addr_r}`) instead of `${fdtcontroladdr}`.

### Boot (board)

Boot-mode switches on QSPI flash (the board's own SPL -> OpenSBI -> U-Boot),
card in the micro-SD slot, USB-serial adapter on UART0 (40-pin header: GND,
GPIO5 TX, GPIO6 RX) at 115200 8N1. Stop autoboot and run, without `saveenv`:

```
mmc list                                   # micro-SD is the 0x16020000 controller, normally mmc 1
setenv devtype mmc; setenv devnum 1; setenv distro_bootpart 1
load mmc 1:1 ${scriptaddr} /boot.scr; source ${scriptaddr}
```

### Expected serial markers

Boot 1 (fresh card), in this order (other diagnostic lines interleave):

```
[u-boot] SimpleOS riscv64 boot.scr devtype=mmc devnum=1 part=1
Starting kernel ...
[console] fdt-selected snps,dw-apb-uart base=0x10000000 reg-shift=2 reg-io-width=4 lsr=0x10000014 stdout-path=alias
=== SimpleOS RV64 NVFS root boot ===
[rv64-nvfs] dw-mshc@0x16020000: SD card ready, 0x<n> sectors
[rv64-nvfs] NVFS superblock found on dw-mshc@0x16020000 partition 2 (start 0x<p2>)
[rv64-nvfs] NVFS root device dw-mshc@0x16020000 start 0x<p2> sectors 0x800
[NVFS] mounted as root filesystem provider=nvfs-dbfs-backed-v1
[rv64-nvfs] ls / : /etc/motd
[rv64-nvfs] ls / : /bin/hello.spl
[rv64-nvfs] cat /etc/motd: SimpleOS NVFS POSIX root ...
[rv64-nvfs] NVFS persistence check: written:first-boot
[rv64-nvfs] write+read /rv64-sanity.txt ok
[rv64-nvfs] exec /bin/hello.spl (loaded from NVFS root)
NVFS_PROGRAM_HELLO_OK hello from a program stored on the NVFS root
NVFS_RV64_ROOT_SANITY_PASSED
```

(`<p2>` is the partition-2 start sector, recorded in decimal as
`sdcard_nvfs_p2_start` in the gate receipt; the kernel prints it in hex —
0x3a000 for the image the gate built on 2026-10-04.) With an eMMC module fitted, a
`dw-mshc@0x16010000: dw-mshc: no SD card answered ACMD41 ...` line precedes
the SD lines.) Boot 2, after a cold power cycle and the same three U-Boot
commands, must additionally show `[rv64-nvfs] ls / : /boot-marker.txt` and
`[rv64-nvfs] NVFS persistence check: persisted:match content=nvfs-persist-ok`.
`NVFS_ROOT_BOOT_FAILED` means no NVFS root was found or mounted — it is a FAIL,
never a fallback. A board PASS needs board identity (U-Boot banner / `mmc
info`), the commands above and both transcripts, per
`.claude/rules/board-runnable.md`.
