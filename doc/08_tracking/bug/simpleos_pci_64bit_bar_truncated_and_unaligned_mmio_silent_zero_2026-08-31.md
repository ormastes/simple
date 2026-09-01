# SimpleOS VFS round-trip blocker 2: 64-bit PCI BAR truncated, and unaligned MMIO reads silently return 0

Date: 2026-08-31
Gate: `scripts/check/check-simpleos-vfs-server-roundtrip-ovmf.shs`
Base: PR #178 (`fix/simpleos-pcimgr-optional-unwrap`), which fixed blocker 1.

Both defects below are FIXED (not routed around).

## Symptom

Under real OVMF pflash the NVMe driver refused the controller with
`nvme-missing-nvm-command-set`. MMIO reads at `bar0_virt` returned
`vs=0x0807005A` (not a legal NVMe version) and a `csts` byte-identical to
CAP's high dword. The driver's refusal was CORRECT; the reads were wrong.

## Ground truth (QEMU HMP, same VM, real firmware)

    info pci -> Bus 0, device 4: 1b36:0010
                BAR0: 64 bit memory at 0xc000004000 [0xc000007fff]
    xp/4wx 0xC000004000 -> 0x0f0107ff 0x00401820 0x00010400 0x00000000

So CAP = 0x00401820_0F0107FF and VS = 0x00010400 (NVMe 1.4) at the physical
BAR. The device and its BAR assignment were never the problem: the bug was
entirely guest-side.

## Defect A — `pcimgr_get_bar` truncated 64-bit memory BARs

`src/os/services/pcimgr/pcimgr.spl`. `pci_read_bar()` returns a `u32` (one
config dword). `pcimgr_get_bar` did:

    val phys_addr = if is_mmio: (raw & 0xFFFFFFF0).to_u64() ...

A 64-bit memory BAR (type bits 2:1 == 0b10) occupies TWO consecutive config
dwords; the upper 32 address bits live at `0x10 + (n+1)*4` and were never
read. OVMF/q35 puts the NVMe BAR at `0xC000004000`, so the low dword is
`0x00004004` and `phys_addr` came out as `0x00004000`.

That is why the failure was silent rather than a fault: `0x4000` is a valid,
mapped, identity-mapped RAM address, so `mmio_read32` happily returned RAM
bytes. It also missed the `NVME_BAR_PHYS_BASE` high-window test in
`_NvmeDriver.init_from_grant`, taking the `SYS_MAP_BAR` path instead of the
pinned higher-half VA — a second wrong turn caused by the same truncation.

`pcimgr_bar_size` had the same blind spot (single-dword probe/restore).

Fix: added `pcimgr_bar_is_64bit(raw)`; `pcimgr_get_bar` composes
`(raw_hi << 32) | (raw & 0xFFFFFFF0)`, and `pcimgr_bar_size` runs the
all-ones probe across both dwords and restores both.

Verified in-guest: `bar0_phys=0xC000004000 size=16384`,
`cap=0x00401820_0F0107FF`, `vs=0x00010400`, `csts=0` — byte-identical to the
QMP ground truth above. The controller then disables, enables, identifies,
reports 131072 x 512-byte sectors (matching the 64 MiB image) and creates its
I/O queues.

## Defect B — unaligned MMIO reads silently returned 0

`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`.
`rt_mmio_read_u16/u32/u64_real` each began:

    if ((uint64_t)addr < 0x1000u || (((uint64_t)addr) & 0x1u)) return 0;

These helpers serve BOTH device MMIO and unaligned RAM scratch reads. The
FAT32 BPB puts bytes-per-sector at byte offset 11 of the boot sector — an odd
address — so `bps` read back as 0 and every FAT32 mount was refused as
"fat32 scalar geometry invalid". Every field at an even offset was correct
(`spc=1 reserved=32 fats=2 fat_size=1009 root=2 t32=131072 sig=0xAA55`),
which is what made this diagnosable. Note the Simple-side comment in
`direct_fat32_boot_reader.spl` already asserted "x86 RAM scratch reads may be
unaligned, so a direct 16/32-bit load is safe here" — the C stub silently
disagreed.

Returning a plausible value for a load that never executed is the same
fail-open shape this tree bans elsewhere. x86-64 permits unaligned 16/32/64-bit
loads, so the alignment rejection was never correct on this target. Fix: drop
the alignment rejection, keep the null-page guard (a sub-0x1000 address is a
real programming error, not a legal unaligned access). Aligned behaviour is
unchanged.

After this fix the guest reaches `fat32 scalar mount ready`.

## Not the cause (checked, recorded so the next lane does not re-derive)

- **PCI memory-space decoding**: `pcimgr.spl:216-217` already sets COMMAND
  bits 1|2. The observed values were never `0xFFFFFFFF`, which argues against
  a disabled decode independently.
- **`mmio_read32/64` miscompiled** (blocker-1 class): `nm` on the built kernel
  shows `rt_mmio_read_u32/u64` as real `T` symbols resolving to the x86_64
  `baremetal_stubs.c` definitions — no weak or synthesized stub. Once the BAR
  address was correct the reads matched QMP byte-for-byte, so the lowering is
  sound.

## Open, NOT fixed — next blocker

`vfs_boot_init_production` requires a pre-provisioned SimpleOS root: it fails
closed on `/VERSION.TXT` (`vfs_boot_state.spl:655`) and then on an ELF at
`BROWSMF.SMF`. The gate mints a bare `mkfs.vfat` volume that starts EMPTY *by
design* (its header explains why: every byte read back must be a byte the
guest itself wrote). So the gate's artifact and the production init contract
are mutually unsatisfiable as written. This is an artifact/contract mismatch,
not a driver defect, and the production check must NOT be weakened to make the
lane green. L3-L8 remain RED.

## Latent, filed not chased

`examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s` fills the high MMIO
PD with `0x83` (PS|RW|P) — no PCD/PWT, so the NVMe BAR is mapped write-back
cacheable. QEMU dispatches MMIO by physical address regardless of guest
cacheability, so this is not the QEMU symptom, but it is a real defect for the
board-runnable rule and should be `0x9B` (PS|RW|P|PCD|PWT) on hardware.
