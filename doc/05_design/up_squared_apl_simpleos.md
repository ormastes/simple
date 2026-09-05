# Detail design: SimpleOS on UP Squared Apollo Lake

## Build and package

`build-simpleos-up-squared-apollo-lake.shs` compiles the dedicated entry for
`x86_64-unknown-none` with the admitted self-hosted compiler. It emits the
Simple closure as an archive, then links that archive with the board-owned
Multiboot CRT and the real simple-core/C runtime capsule. The direct kernel
link must reject any retained `simpleos_syscall`; the
`x86_64-unknown-simpleos` filesystem-process entry shim is not part of this
lane.
`build-simpleos-up-squared-usb-image.shs` verifies the kernel receipt, invokes
the generic GPT/FAT32 x64 UEFI packager, checks the image, then records kernel,
BOOTX64.EFI, and whole-image hashes. The kernel retains a legacy Multiboot1
header but also publishes the required Multiboot2 header for its ELF64 UEFI
lane. GRUB emits loader-ready and kernel-admitted markers around `multiboot2`.

## Removable-media admission

`write-simpleos-up-squared-usb.shs` is read-only unless `--write-media` is
present. It requires a stable `/dev/disk/by-id` symlink and exact serial,
resolves a whole removable USB disk, rejects mounts, holders, root/swap backing,
identity races, and insufficient capacity, then prints a SHA-256 challenge over
by-id, serial, capacity, and image hash. Root plus the exact challenge authorizes
one image write. The script flushes, hashes exactly the image-length bytes from
the device, rechecks identity, and emits a read-only receipt.

## Boot and shell evidence

The kernel emits `UP2 entry`, `UP2 console-ready`, `UP2 filesystem-ready`, and
`UP2 shell-ready`. The checker keeps one UART capture open, waits for shell,
sends exactly `ls /`, and requires `/bin`, `/etc`, and `/README.txt` between
`UP2 ls-begin source=vfs command=ls /` and `UP2 ls-end status=pass`.

The first-light console remains explicitly a live-unproven legacy-COM1
candidate. If CN16 firmware routing does not expose that port, the next board
provider must discover the Apollo Lake LPSS UART; no marker may claim the
candidate proven before physical evidence.

## Shared NVMe provisioning

`up_squared/nvme_storage.spl` is a board adapter, not a second NVMe driver. It
uses `pcimgr` for x86 PCI discovery/grant and delegates controller state,
queues, DMA, sector I/O, GPT, and FAT32 to common modules. `nvme identify` is
read-only and prints the exact `FORMAT:<serial>:<nsid>:<lba-count>` token.
Only `nvme format <exact-token>` commits. The commit writes mirrored GPT,
formats the partition lease, creates a valid `PROOF.TXT` FAT chain/directory
entry, flushes, opens a fresh adapter, and verifies the file bytes. `ls /nvme`
rechecks the on-media boot signature, directory entry, and payload.

The UP2 freestanding runtime supplies coherent x86 DMA pool/sync primitives
and volatile MMIO, while `NvmeDriver` stays the canonical mutable owner. The
Identify fields use an exact hex representation so the serial challenge does
not depend on hosted UTF-8 conversion.
