# aarch64 real-firmware EFI lane was unreproducible; unified arm64 lane still uses QEMU `-kernel`

- **Date:** 2026-08-11
- **Status:** PARTIALLY FIXED — EFI lane is now reproducible and gated (GREEN).
  The `-kernel` dependency of the main arm64 desktop lane REMAINS OPEN.
- **Rule:** `.claude/rules/board-runnable.md`

## The filed claim was stale

`.claude/rules/board-runnable.md` said *"aarch64 currently lacks an EFI-stub —
that gap is filed"*. Measured on 2026-08-11, that is **not** what was missing.
The aarch64 real-firmware boot path already existed and already worked:

```
$ sh scripts/check/check-simpleos-aarch64-limine-framebuffer.shs
PASS — real-firmware (EDK2/AAVMF pflash + Limine BOOTAA64.EFI) aarch64 boot
obtained a framebuffer: addr=0x18446462600284340224 800x600 bpp=32 pitch=3200;
3 refusal paths checked and none fired
```

Host firmware is present (`/usr/share/AAVMF/AAVMF_CODE.fd`,
`/usr/share/AAVMF/AAVMF_VARS.fd`, `/usr/share/qemu-efi-aarch64/QEMU_EFI.fd`), and
`vendor/limine/BOOTAA64.EFI` is git-tracked. Rule text corrected in this change.

## What was actually broken (1): the boot artifact had no builder

`build/os/aarch64_limine/esp.img` was a **one-off hand-made artifact**. Per
`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`
it was populated "via the `pyfatfs` venv at `/tmp/pyfatvenv`" — a throwaway
virtualenv outside the repo, which no longer exists. Confirmed:

- `git ls-files build/os/aarch64_limine/` -> **empty** (`build/` is gitignored).
- `grep -rn aarch64_limine` across `*.shs *.spl *.sh` -> the only non-doc hit is
  the gate that *consumes* the image. **No producer existed anywhere.**
- No `mtools`, no system `pyfatfs`, and `/tmp/pyfatvenv` gone.

So a clean clone could not produce a bootable aarch64 EFI artifact at all. The
lane passed only because a binary happened to survive in a gitignored directory.

**Fixed** by `scripts/os/build-simpleos-aarch64-efi-esp.shs`, which builds the
ESP from tracked inputs (`vendor/limine/BOOTAA64.EFI` + the kernel ELF), with a
`mkfs.vfat` FAT32 filesystem, a repo-local pyfatfs build venv created on demand,
and a **read-back verification pass** so a silently-truncated FAT write cannot
report success.

### Design choice: EFI *application* chain, not a PE/COFF kernel stub

Deliberate, and the smaller diff. The repo already vendors a prebuilt
`BOOTAA64.EFI` and the kernel already speaks the Limine boot protocol
(`src/os/kernel/boot/limine_boot_aarch64.spl`), so zero compiler or linker work
is needed — this mirrors x86_64, which also chains through an EFI application on
a FAT ESP rather than stubbing the kernel. A PE/COFF stub would require PE
emission from the Simple backend, which does not exist. Rationale is recorded in
the build script header, not only here.

## What was actually broken (2): the main arm64 lane still uses `-kernel` — STILL OPEN

`scripts/check/check-simpleos-arm64-unified-live.shs:233` boots with:

```
    -kernel "$kernel" -device ramfb \
```

QEMU `-kernel` pass semantics do not exist on hardware. Under
`.claude/rules/board-runnable.md` this makes the **main arm64 desktop/WM lane
QEMU-only**, regardless of the EFI lane now being green. This is **not** fixed
here and is not narrowed away: the new gate proves the real-firmware chain
independently so that lane can be *migrated onto it* rather than blessed.

**Remaining work for full x86_64 parity:**
1. Migrate `check-simpleos-arm64-unified-live.shs` off `-kernel` onto the
   AAVMF + `BOOTAA64.EFI` + ESP chain proven here.
2. Give the unified arm64 kernel a from-source build in the ESP builder.
   `KERNEL_ELF` is currently an *input*; the kernel's own seed `native-build`
   lane (`--backend cranelift --target aarch64-unknown-none-elf --linker-script
   .../linker_limine.ld`) is not invoked by the builder, which fails loudly
   rather than inventing a kernel. So the ESP is reproducible; the kernel inside
   it is not yet.
3. Physical board bring-up for aarch64 remains filed as before.

## Evidence — red then green

**RED.** `esp.img` deleted; before this change nothing in the repo could
regenerate it (`grep` for a producer returns nothing).

**GREEN.** Rebuilt from tracked inputs by the new builder:

```
[esp] firmware  CODE=/usr/share/AAVMF/AAVMF_CODE.fd
[esp] bootloader vendor/limine/BOOTAA64.EFI
[esp] kernel     build/os/aarch64_limine/kernel.elf (105736 bytes)
[esp]   /EFI/BOOT/BOOTAA64.EFI  274432 bytes
[esp]   /boot/kernel.elf  105736 bytes
[esp]   /limine.conf  127 bytes
[esp]   /startup.nsh  28 bytes
[esp] sha256 b25466a830c411b0266110b1b873d069dc3d059163ffab374b558fa7102269c0
```

Booted under EDK2/AAVMF pflash (no `-kernel`, no `isa-debug-exit`), 76 serial
lines, verbatim excerpts:

```
[BOOT] HHDM offset: 0x18446462598732840960
[BOOT] Memory map: 46 entries
[BOOT]   region 0: base=0x67108864 size=0x67108864 type=1
[BOOT] Framebuffer: addr=0x18446462600284340224 800x600 bpp=32 pitch=3200
[BOOT] Handing off to memory layer...
[BOOT] memory_init: wiring Layer 1 physical memory manager (aarch64, Limine lane)
[BOOT] SIMPLEOS-AARCH64-LIMINE-KERNEL-OK
```

Gate verdict:

```
PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64
boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit),
76 serial line(s) captured
```

## Gate is not tautological

`scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` was sabotage-verified:

| variant | verdict | exit |
|---|---|---|
| real ESP, AAVMF pflash | `PASS — 4 boot-stage marker(s) checked ...` | 0 |
| ESP whose `/boot/kernel.elf` is 105,736 random bytes | `FAIL — ... never printed ...` | 1 |
| artifact dir empty (`SKIP_ESP_BUILD=1`, no `esp.img`) | `ERROR — nothing was checked: missing .../esp.img` | 2 |

It requires **four** positive boot-stage markers, so a partial boot (firmware up,
kernel wedged early) cannot pass; an empty serial log is ERROR, never PASS; and
it asserts the absence of `-kernel` / `isa-debug-exit` against the **assembled
argv it is about to execute**, not against its own prose.

## Files

- `scripts/os/build-simpleos-aarch64-efi-esp.shs` (new) — reproducible ESP builder.
- `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` (new) — the gate.
- `.claude/rules/board-runnable.md` — stale claim corrected, real gap restated.
