# aarch64 SimpleOS: real-firmware boot gap + 2 seed/driver defects (launch sanity, 2026-07-14)

Found by Lane LAUNCH-OS-AARCH64 doing a real launch sanity check. The aarch64
kernel boot gate (loader + FS-exec staging) reproduces GREEN
(`ARM64_SIMPLE_TOOL_GATE_PASS` / `TEST PASSED`, `e_machine=183`, QEMU self-exit
via semihosting) and the WM readiness check is READY. These three items are the
honest gaps/defects behind that green, so the workarounds are not silently
normalized.

## 1. No real-firmware (EDK2/UEFI) boot path on aarch64 — board-proxy gap

The board-proxy rule wants boot via real firmware, not QEMU `-kernel` pass
semantics. On **riscv64** this is automatic: `-kernel` loads the kernel as an
S-mode payload *through* OpenSBI, so BR64 satisfies the rule. On **x86_64** we
use OVMF pflash. **aarch64 has no such analog today:** the probe kernel is a
pure bare-metal ELF (entry `0x40200000`, crt0 does the EL2→EL1 drop) with **no
PE/EFI-stub, no arm64 `Image` header, no multiboot header**. So:

- `qemu-system-aarch64 -machine virt -kernel bareELF` boots it directly at EL1
  with **no firmware** — works, but is not a firmware boot.
- `-bios AAVMF(EDK2) -kernel bareELF` → EDK2 boots (`UEFI firmware version
  2024.02`) but **cannot load the bare ELF** (`BdsDxe: ... Not Found`, zero
  kernel markers) because it has no EFI entry.

**Fix (concrete follow-up, not a regression):** give the aarch64 kernel a UEFI
**EFI-stub** (PE/COFF header + `efi_main` that sets up and jumps to the existing
entry), OR provision an aarch64 bootloader (arm64-efi GRUB or aarch64 U-Boot) as
the pflash payload that then loads the ELF. Local tooling is currently missing
(no arm64-efi GRUB platform, no aarch64 U-Boot, and curl/wget are blocked), so
this needs either the EFI-stub in-tree or a provisioning step. Until then the
aarch64 "board proxy" is EL1-direct `-kernel`, which is weaker than x86/riscv.

## 2. Seed cranelift miscompiles `_arm_fat32_find_sys_cluster` on spc=8

The bootstrap seed's cranelift backend miscompiles the arm64 VFS helper
`_arm_fat32_find_sys_cluster` when sectors-per-cluster == 8: it reads garbage
from FAT32 directory data that a sibling function reads correctly. Worked around
in `src/os/services/vfs/arm_fs_exec_vfs.spl:409` (root-scan + inline byte
matcher instead of the miscompiled path). Real fix belongs in the seed cranelift
codegen (arm64) or the #99 self-hosted redeploy. Same class as the x86_64 seed
enum-payload miscompile.

## 3. arm64 virtio-blk descriptor ring is single-sector-only

The arm64 baremetal virtio-blk driver descriptor ring reads only one sector per
request; a multi-sector `read_prefix` corrupts data past sector 0. VFS currently
reads cluster data sector-by-sector as a workaround
(`src/os/services/vfs/arm_fs_exec_vfs.spl:265`), which is why the staged
`/simple.elf` returns 529502 of 4.2MB (enough to validate the ELF header, not to
run it). Note at `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:2578`.
Fix: multi-descriptor chaining in the arm64 virtio-blk ring so a whole cluster
(or larger prefix) transfers in one request.

## Status

Boot + loader/FS-exec staging on aarch64 is GREEN with these workarounds. Full
in-guest U-mode Simple RUN stays blocked on the #99 seed-cranelift enum
miscompile (all arches). Items 1-3 are the concrete follow-ups; none is a
regression.
