# Architecture: SimpleOS on UP Squared Apollo Lake

## Outcome and trust boundary

The lane produces a dedicated x86_64 Multiboot kernel, packages it in the x64
UEFI removable fallback path, admits exactly one removable USB identity, and
accepts physical boot only from one fresh UART session. Offline image checks
and prerecorded logs cannot become a board PASS.

## Layers

1. **Board kernel** — `src/os/kernel/arch/x86_64/up_squared/` owns entry,
   console, immutable packaged root, and public-VFS shell integration.
2. **Admitted build** — the board build wrapper binds the self-hosted compiler,
   freestanding runtime capsule, linker, kernel hash, and provenance receipt.
3. **UEFI package** — the UP2 image wrapper embeds that exact kernel in
   `EFI/BOOT/BOOTX64.EFI`, verifies GPT/FAT32 structure, and emits an image
   receipt. It has no block-device write authority.
4. **Media admission** — the separate writer accepts only an explicit
   `/dev/disk/by-id` whole USB disk whose serial, removability, capacity,
   mount/holder state, and non-system status pass. Write authority requires an
   identity-and-image-bound challenge; full image-length readback is mandatory.
5. **Physical oracle** — one bounded Tigard UART session observes ordered
   entry/console/filesystem/shell markers, sends `ls /`, and accepts entries
   only inside the fresh VFS command window.

The lane never writes eMMC, SATA/NVMe, BIOS/SPI, UEFI variables, or CN22. F7
one-time boot selection is an operator action, not persistent firmware state.

## Failure semantics

Absent media, privilege, Tigard, or board UART evidence is BLOCKED. Unsafe or
changing media identity, connected-board boot failure, malformed marker order,
or uncorrelated `ls` is FAIL. Only complete receipts plus physical UART evidence
produce PASS.
