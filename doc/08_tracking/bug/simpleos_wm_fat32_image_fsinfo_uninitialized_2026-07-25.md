# SimpleOS-WM cell: staged FAT32 image fails `fsck.fat` — FSInfo sector never initialized; gate also treats fsck warnings as failures

- **ID:** simpleos_wm_fat32_image_fsinfo_uninitialized_2026-07-25
- **Status:** OPEN — characterised, not fixed
- **Severity:** medium — blocks the `SimpleOS-WM × QEMU` showcase-matrix cell at
  the disk-staging stage (the stage *after* the kernel build + ELF admission,
  both of which now pass)

## Where the cell is now

Four blockers have been cleared on this cell today, each revealing the next:

| # | blocker | status |
|---|---|---|
| 1 | `fn cli():` parsed as a reserved token | fixed (`d5a6312da1b`) |
| 2 | `hir: struct 'ANY' field 'left_just_pressed'` (duplicate `MouseEvent`) | fixed (`a163f3977a2`) |
| 3 | ELF gate asserted ELF64/EM_X86_64 on the ELF32 multiboot wrap | fixed by gate owner |
| 4 | **this** — staged FAT32 image fails `fsck.fat` | OPEN |

Current status keys:

```
simpleos_wm_fullscreen_kernel_build_status=current-source-built   <-- kernel OK + admitted
simpleos_wm_fullscreen_disk_image_status=invalid-fat32-structure
simpleos_wm_fullscreen_reason=production-fat32-disk-invalid
```

## Measurement

Image: `build/simpleos_wm_fullscreen_evidence/fat32-x86_64-font.img`,
134,217,728 bytes (128 MiB), staged by
`scripts/os/make_os_disk.shs 26 <img> <kernel> x86_64` (which exited **0** —
it does not consider the result invalid).

Geometry read from the boot sector: `sectors_per_cluster=8` (4 KiB clusters),
`reserved_sectors=32`, `fsinfo_sector=1`.

Header fields the harness's own pre-checks accept (all correct):
`jump=eb5890`, OEM=`SIMPLEOS`, `bytes_per_sector=0x0200`, boot signature `55aa`.

`fsck.fat -n` (true exit code **1**) reports three things:

1. **FSInfo sector is all zeros — the one hard defect.**
   ```
   FSINFO sector has bad magic number(s):
     Offset 0:   0x00000000 != expected 0x41615252
     Offset 484: 0x00000000 != expected 0x61417272
     Offset 508: 0x00000000 != expected 0xaa550000
   ```
   The boot sector *declares* FSInfo at sector 1, but sector 1 was never
   written.
2. **Backup boot sector (sector 6) is all zeros** — the boot sector declares
   `backup_boot_sector=6`. fsck calls this *"mostly harmless"*.
3. **32,731 clusters, below the FAT32 minimum of 65,525** — fsck: *"This may
   lead to problems on some systems."* At 4 KiB clusters, reaching 65,525
   clusters needs ~262 MiB of data area, so a 128 MiB image cannot satisfy it
   without smaller clusters (`sectors_per_cluster=2` → ~131 K clusters).

## Two separable problems

### A. The image really is missing FSInfo (fix the builder)

Note there is **more than one FAT32 writer in-tree, and they disagree**:

- `src/os/port/disk_image.spl` **does it correctly**: `_build_fsinfo()` writes
  `0x41615252` / `0x61417272` (lines ~396-400) and the boot sector sets
  `backup_boot_sector=6` (line ~374), with `sectors_per_cluster=1` (line ~357).
- The **staged image** has `sectors_per_cluster=8` and a zeroed FSInfo — so it
  was **not** produced by that builder.

I did not finish tracing which writer `make_os_disk.shs` actually reaches
(it delegates; `src/app/simpleos_tool/main.spl` is referenced at line ~66).
**Next step: identify the writer actually used, then either fix its FSInfo/backup
emission or route staging through `disk_image.spl`, which already gets it right.**
This is another same-name/duplicate-implementation divergence (see glossary:
*Same-Name Divergence*).

### B. The gate treats fsck *warnings* as failures (possibly over-strict)

`fat32_image_status()` gates on `fsck.fat -n "$img"` exit status. `fsck.fat`
returns non-zero for advisories too — of the three findings above, fsck itself
labels #2 "mostly harmless" and #3 "may lead to problems", i.e. only #1 is a
structural error. So the current gate cannot distinguish "image is broken" from
"image is unusual but bootable".

This is the **same over-strict-gate pattern** as the ELF check on this very
harness (which demanded EM_X86_64 of a deliberately ELF32 multiboot image — see
`simpleos_x86_64_kernel_links_as_elf32_em386_2026-07-25.md`). Before relaxing
anything, fix (A): if FSInfo is written and the cluster count is brought in
spec, fsck should pass cleanly and the question of warning-vs-error becomes moot.
**Do not relax the gate to go green while the image is genuinely missing FSInfo.**

## Verification note

`fsck.fat -n "$img" | head` reports the exit code of `head`, not `fsck` — it
looked like `rc=0` on first measurement. Get the real code with a bare
`fsck.fat -n "$img" >/dev/null 2>&1; echo $?`. Same pipeline-exit-code trap
recorded in `.claude/skills/spipe.md`.
