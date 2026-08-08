# SimpleOS-WM cell: staged FAT32 image fails `fsck.fat` — FSInfo sector never initialized; gate also treats fsck warnings as failures

- **ID:** simpleos_wm_fat32_image_fsinfo_uninitialized_2026-07-25
- **Status:** RESOLVED — `fsck.fat` exits 0 on the staged image (`37cda4b`)
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

## FIXES LANDED 2026-07-25 (`scripts/os/make_os_disk.c`)

The writer is **C**, not Simple: `make_os_disk.shs` does
`cc -O2 -std=c99 ... scripts/os/make_os_disk.c -o build/os/make_os_disk` and
execs it. `src/os/port/disk_image.spl` — which writes FSInfo correctly — is NOT
in this path. Two independent FAT32 writers exist and only the unused one was
correct.

All structural errors are now cleared: the image reports
**`98 files, 15084/32731 clusters`** and is fully traversable. Seven defects
fixed, each only visible once the previous cleared:

| # | defect | fix |
|---|---|---|
| 1 | BPB declares `fsinfo_sector=1`, sector 1 all zeros | write lead/struct/trail magics at +0/+484/+508 |
| 2 | BPB declares `backup_boot_sector=6`, sector 6 all zeros | `memcpy` sector 0 → sector 6 |
| 3 | 11 subdirectories had no `.`/`..` entries | `put_dot_entries()` helper, parent-mapped |
| 4 | hardcoded `fonts_n != 91` guard tripped by the 2 new dot entries | expected total → 93, guard kept |
| 5 | two entry pairs shared one cluster chain (FAT32 has no hard links) | independent `*_alias` allocations |
| 6 | `/TMP` had a cluster + root entry but **no content buffer** — never written | added buffer, dot entries, `memcpy` |
| 7 | volume label absent (boot sector **and** root `ATTR_VOLUME_ID` entry) | write both, matching spelling |

Also: FSInfo `free_count`/`next_free` now carry real values instead of
`0xFFFFFFFF` ("unknown", which fsck flags), and the two orphaned
`steam_manifest`/`steam_marker` allocations are removed with a
`TODO(simpleos-steam-staging)` — their staging was never wired, and the
compiler's own unused-variable warnings had been pointing at it.

### RESOLVED — fsck now exits 0 with zero findings

A parallel session took the fixes above and added the piece this investigation
had explicitly declined to attempt: **dynamic geometry selection**. Measured on
the merged builder at `37cda4b`:

```
fsck.fat -n <img> >/dev/null 2>&1; echo $?   ->  0
105 files, 60309/130546 clusters
```

No warnings, no reclaimed clusters, no free-count mismatch. All three items
previously listed here as open are gone, and none of them needed to be chased
individually:

- **52 orphaned clusters** — gone. Never located by source scanning, and did not
  need to be: they were an artifact of the fixed `SECTORS_PER_CLUSTER = 8`
  geometry. Time spent hunting individual `alloc_clusters` call sites was wasted
  effort against a symptom.
- **`Free cluster summary wrong`** — gone, exactly as predicted: it was a
  consequence of the leak, not an independent defect.
- **32,731 clusters < 65,525** — **fixed, not worked around.** This doc had
  called it "deliberately untouched" on the grounds that changing cluster size
  would disturb the kernel FAT driver. That judgement was too conservative.
  `geometry_for_cluster_size()` now searches candidates {64,32,16,8,4,2,1} for
  the largest cluster size still yielding >= `FAT32_MIN_DATA_CLUSTERS`, and
  `reserve_clusters()` bounds-checks against the resulting FAT extent. The image
  now reports 130,546 clusters and is spec-conformant.

The merged builder also supersedes three fixes recorded above with cleaner
forms: `write_directory()` replaces the hand-rolled `/TMP` `memcpy`, a shared
`write_fat32_fsinfo()` serves both sector 1 and the sector-7 backup, and the
`steam_*` clusters are **wired into real directory entries** rather than deleted
— so the `TODO(simpleos-steam-staging)` is discharged, not deferred.

### Landmine: this file was pushed as a jj conflict commit

Commit `857e26b0cbc` (the FAT32 fix) was pushed while
`scripts/os/make_os_disk.c` was still 2-sided-conflicted. jj encodes a
conflicted commit in git as a tree containing only `.jjconflict-base-0/`,
`.jjconflict-side-0/`, `.jjconflict-side-1/` — **no real files at all**. The
FPGA commit stacked on top and inherited it, so `main` on GitHub had an empty
tree across two commits until `37cda4b` restored it.

`jj st` showed the conflict locally; the push was not blocked. The pre-push
guard in `.claude/rules/vcs.md` exists for exactly this and was not run. Check
before every push:

```sh
git ls-tree --name-only <tip> | grep '^\.jjconflict' && echo "DO NOT PUSH"
```

Note that `git cat-file -p <sha>:<path>` on such a commit reports *"exists on
disk, but not in <sha>"* — which reads like a missing file, not a broken tree.
`git ls-tree` on the commit is what makes the real cause obvious.

### Method note (cost real time twice)

A first orphan scan reported **five** orphans. Three were **false positives**:
`put_dir_entry(...)` calls that wrap onto a second line, invisible to a
single-line grep. Acting on it would have deleted three genuinely-used
allocations and broken the font bundle. Counting total occurrences of each
variable gave the correct answer (two). Prefer occurrence-counting over
pattern-matching a call shape in this file — multi-line calls are common.

## Verification note

`fsck.fat -n "$img" | head` reports the exit code of `head`, not `fsck` — it
looked like `rc=0` on first measurement. Get the real code with a bare
`fsck.fat -n "$img" >/dev/null 2>&1; echo $?`. Same pipeline-exit-code trap
recorded in `.claude/skills/spipe.md`.
