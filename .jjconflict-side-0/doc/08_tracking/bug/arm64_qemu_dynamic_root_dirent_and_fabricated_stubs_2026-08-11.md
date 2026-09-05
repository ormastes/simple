# ARM64 QEMU Dynamic Root Dirent and Fabricated-Stub Blockers

**Date:** 2026-08-11  
**Status:** STATIC REPAIR PRESENT — fresh build/live proof still pending  
**Acceptance criteria:** AC-5, AC-6, AC-7, AC-14

## Evidence

The ARM64 image, mounted user ELF, and kernel were built and booted under the
canonical QEMU descriptor. The guest proves boot, VirtIO-BLK initialization,
FAT32 BPB parsing, VFS mount, and SMF loading. The final retained attempt is:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/arm64/20260811T064000Z/
```

The generated image contains root entry `FSEXEC  ELF` at byte offset 539040,
and the staged AArch64 ELF is 4904 bytes. Nevertheless,
`arm_fs_exec_read_file_bytes("/FSEXEC.ELF")` returns zero bytes. Adding the
missing alias and explicit literal dirent comparison did not change the result.

The kernel build also requires `SIMPLE_ALLOW_FREESTANDING_STUBS=1` and
fabricates 108 previously unbaselined weak return-zero bodies. This independently
disqualifies the artifact from release evidence.

## Unblock conditions

1. Add bounded target diagnostics to the dynamic root scan at the observed
   root offset and prove whether entry traversal, short-name dispatch, cluster
   extraction, or file-chain reading fails.
2. Remove the broad closure responsible for 108 fabricated symbols or provide
   real freestanding implementations; do not baseline fabricated behavior.
3. Add real guest directory enumeration markers.
4. Rebuild without fabricated stubs, boot once, execute `/FSEXEC.ELF`, and
   classify nonce-correlated stdout/exit evidence.

No further ARM64 build/boot retry is permitted in the originating session.

## Ownership

- Owner: ARM64 SimpleOS execution lane
- Merge owner: SOSIX/QEMU integration lane
- Final reviewer: independent normal/highest-capability reviewer

## Static root-cause follow-up (2026-08-11)

The retained serial trace narrows the zero-byte read to route selection, before
directory matching or file-chain copying:

```text
[vfs-read] path=/FSEXEC.ELF mapped=/FSEXEC.ELF
[arm-fs-trace] 230
[arm-fs-trace] 225
```

Trace `225` is emitted only by `_arm_fat32_find_apps_cluster`; trace `240`, the
root-file route, is absent. Thus the correctly mapped root path entered the
`/SYS/APPS/` branch in the retained freestanding build. The bounded repair now
routes the three root-staged files by exact equality before any prefix checks
and uses the BPB-derived `g_arm_root_cluster` for every root scan.

The retained ELF is still available at
`/mnt/data/.simple/qemu/images/arm64/fs-exec-v1/simpleos_arm64_fs_exec-v3.elf`.
Its symbol table shows that section GC retained two of the 108 generated weak
return-zero bodies:

```text
rt_array_copy  size=8 weak
rt_enum_id     size=8 weak
```

Real ARM64 definitions for both symbols have been added using the existing
ARM64 array and enum layouts. The canonical QEMU runner already excludes
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` for ARM64 fs-exec; a future clean build must
therefore use that fail-closed path and prove zero fabricated symbols.

No ARM64 build or boot was run in this follow-up because the originating lane's
three-cycle cap remains authoritative. The focused static spec is
`test/01_unit/os/services/vfs/arm_fs_exec_root_route_spec.spl`.

## Static repair verification (2026-08-11)

The working source now places exact root-file routing for `/FSEXEC.ELF`,
`/SIMPLE.ELF`, and `/HELLO.SPL` before `/SYS/APPS/` prefix routing. Root reads
use the BPB-derived root cluster through `_arm_root_cluster()`. The ARM64
baremetal runtime also contains strong, layout-compatible implementations of
`rt_array_copy` and `rt_enum_id`; neither is a weak return-zero fallback.

Only source guards and a Clang syntax check were run for this repair. A fresh
fail-closed kernel rebuild and live QEMU execution remain required before this
bug can be closed or cited as release evidence.

## FAT multi-sector descent blocker after three live cycles (2026-08-12)

**Status: BLOCKED — three distinct build/live verification cycles exhausted.**
Do not resume this rollout or run QEMU again in the same session.

Retained evidence:

- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-fatfix-20260812T020000Z/serial.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-fatcluster-20260812T021500Z/serial.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-appendfix-20260812T023000Z/serial.log`

All three kernels parse the real BPB as `bps=512 spc=2 reserved=32 fats=1
fat_size=1020 root=2 data_start=1052`, enter path resolution (`230`), APPS/SYS
descent (`225`, `221`), then report cluster trace `251,128`: the first sector
begins with the expected `SIMPLEOS` volume entry, later inspected positions are
zero, and SYS lookup ends at `226`. This contradicts the image itself, whose
root cluster is 1024 bytes and contains the `SYS` dirent at offset 64, followed
by a valid `SYS/APPS/HELLOSMF.SMF` descent. The retained symptom is therefore a
live ARM64 Simple-to-C array length/capacity or append ABI defect, not a missing
dirent and not grounds for a root/fallback lookup.

Current source state removes the cluster-capacity scalar boundary entirely:
`rt_arm_array_new_fat_cluster(void)` allocates the fixed FAT32 maximum of
`128 * 512` bytes in C. Cluster assembly uses the no-limit-crossing
`rt_arm_array_append_sector(dst, src)`, and file-chain assembly uses
`rt_arm_array_append_to_capacity(dst, src)`. Static image descent and AArch64 C
syntax checks pass, but no live acceptance claim is valid because the third
retained run still reports length 128.

Safe fresh-session resume command (diagnose statically before authorizing one
new bounded build/live cycle):

```bash
bin/codex exec -C /home/ormastes/dev/pub/simple 'Resume the ARM64 FAT multi-sector descent blocker recorded in doc/08_tracking/bug/arm64_qemu_dynamic_root_dirent_and_fabricated_stubs_2026-08-11.md. Start from the three retained serial logs; inspect generated ARM64 call/return ABI for rt_arm_array_new_fat_cluster, rt_arm_array_append_sector, and rt_arm_array_len_u32. Do not add a fallback. Permit at most one build and one QEMU run after a falsifiable static diagnosis.'
```

## Fresh bounded construction result (2026-08-12)

One strict ARM64 rebuild/media construction completed with the admitted
Stage2 SHA-256
`2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`.
The retained kernel and image hashes match their receipts and pass the shared
filesystem-exec ELF gate, the ARM64 strong-symbol ELF gate, and the mounted
ARM64 payload gate:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/arm64-real-el0-20260812T-live1/
```

Live verification stopped before QEMU at nonce-media preparation. The helper
uses `dd bs=1` to copy the image tail beginning at byte `1277952`; on this
128 MiB image that process remained at 99% CPU after 4m14s. It was terminated
under the bounded-run rule. No QEMU process started (`qemu_attempts=0`), so
there is no new boot, listing, EL0 stdout, exit-37, resume/reap, or TEST PASSED
claim. The retained blocker receipt is:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-real-el0-20260812T-live1/blocker.env
```

Before another live attempt, replace the byte-at-a-time tail extraction in
`prepare_qemu_nonce_media.shs` with a bounded block-size extraction that keeps
the exact ELF-extent/hash/readback contract, and cover it with the existing
sabotage self-test.

### Nonce preparation performance repair

The helper now patches and reads both slots with exact binary seeks, scans
backward for the owning ELF in 64 KiB blocks, parses ELF32/ELF64 program headers
directly, and extracts only the exact file-backed PT_LOAD extent in 64 KiB
chunks. It no longer creates a whole-image tail or uses `dd bs=1` for that
copy. The output remains a temporary clone renamed atomically; the source is
hash-checked as immutable by the test.

`check-prepare-qemu-nonce-media.shs` retains missing/duplicate-slot and
in-place-mutation sabotage, adds malformed slots-without-ELF sabotage, verifies
the exact image and patched-ELF receipt hashes, and exercises a sparse 128 MiB
image. The realistic gate completed in 2 seconds against a 20-second bound.
No rebuild or QEMU run was performed for this repair.

## Fresh single-boot result after nonce-helper repair

The retained verified kernel/image were nonce-cloned successfully and passed
all patched-media and static ELF gates. Exactly one explicit TCG boot was run:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-real-el0-20260812T-live2/
```

The guest again reports assembled FAT chunks with length `128`, cannot read
`/SYS/APPS/HELLOSMF.SMF`, emits `[arm-fs-exec] vfs:fail` and `TEST FAILED`, and
exits QEMU with status 1. Serial SHA-256 is
`5b8c2c6fef670c91c495074054f165f4a2a700d4a8820524c47e050522397629`.
The target nonce, real `/SYS/APPS` listing, real EL0 stdout, exit 37, kernel
resume/reap, and `TEST PASSED` are all absent. This is diagnostic failure
evidence only and does not promote the ARM64 row.

### Exact remaining ABI/method-resolution cause and source repair

Disassembly of retained kernel SHA
`4439cf7e729835ec117d62a05551a33453c69e817d1dea6034f85d15c0216491`
proves that `rt_arm_array_new_fat_cluster` loads `0x10000` and
`rt_arm_array_append_sector` loads `0x200`; those C owners are correct. The
apparent length `128` was a diagnostic artifact: `arm_fs_exec_trace` treated
the raw return value 1024 as a tagged integer and shifted it right by three.

The real scan failure was the next boundary. Every directory owner used
`rt_arm_array_len_u32(data).to_i32()`, and the retained call site resolves that
method to address `0x4020a948`, whose symbol is the unrelated
`EventKind.to_i32`. Thus the correct raw 1024-byte length never became the
directory-loop bound.

The source repair adds the explicitly typed C ABI owner
`rt_arm_array_len_i32_raw` and uses it directly in all six directory scans,
with no language-level method conversion. Dynamic length/byte traces use
`arm_fs_exec_trace_raw`, so the next kernel will report raw values without the
tagged heuristic. The executable C regression demonstrates that a second-sector
dirent is invisible under the former 1024-to-128 conversion and visible with
the raw signed bound; the static contract also rejects any remaining
`.to_i32()` length conversion. The real FAT image descent remains independently
checked.

Source-only evidence passed:

```text
PASS arm64 FAT raw-capacity descent root=2 sys=14 apps=22 hello=511 spc=2
PASS arm64 FAT raw length ABI regression
AArch64 freestanding C syntax: PASS
```

No rebuild or QEMU run was performed for this source repair, so live closure
remains pending.

## Single live closure result after raw-length repair

One strict cached rebuild/media construction, nonce preparation, and all static
gates passed. Exactly one TCG boot was run from the retained artifacts:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-real-el0-20260812T-live3/
```

The live transcript validates the raw-length diagnosis and repair: the root
cluster is now truthfully reported as `2048`, `SYS` and `APPS` are found,
`HELLOSMF.SMF` is read at offset 64, and VFS reaches ready. The boot then stops
at a distinct root-path routing defect: `/QEMUNONC.TXT` enters the
`/SYS/APPS` route, returns zero bytes, and emits
`[qemu-nonce] target media read failed`. QEMU exits 1. Serial SHA-256 is
`9a30eaab02c72b372d74a2d4b5aecb13110cf04d25aedd26ddbf6917cb7f0737`.

The target nonce, `/SYS/APPS` listing, real EL0 stdout, exit 37, kernel
resume/reap, and `TEST PASSED` are absent. This is diagnostic failure evidence;
the ARM64 matrix row remains unpromoted. The next source repair must route the
exact root-staged `/QEMUNONC.TXT` path before any `/SYS/APPS` prefix/alias
selection, using the BPB-derived root cluster and no fallback.

### Exact root nonce routing repair

The path/short-name tables now explicitly canonicalize `/QEMUNONC.TXT` (and
its lowercase spelling), and the exact root route includes it before the
`/SYS/APPS/` and `/SYS/` prefix branches. It shares the same BPB-derived root
scan as `FSEXEC.ELF`, `SIMPLE.ELF`, and `HELLO.SPL`; no app alias or fallback
was added.

The executable shell/FAT regression proves ordering and absence of a nonce app
alias, then parses the real ARM64 image. It finds the regular 118-byte
`QEMUNONCTXT` dirent at root offset 320 and independently descends the real
root/SYS/APPS/HELLOSMF chain (`root=2 sys=8 apps=12 hello=268`, `spc=4`).
Source checks pass; no rebuild or QEMU run was performed, so live closure is
still pending.

## Interrupted live4 construction blocker

The next single cached construction stopped before linking because the host
root filesystem was full. Object writes failed with `ENOSPC` for exactly the
three changed ARM64 compilation units (`fs_exec_entry.spl`,
`arm_fs_exec_alias.spl`, and `arm_fs_exec_vfs.spl`). `/` reported 100% used
with 1.4 GiB nominally available while `/mnt/data` remained 26% used. No row or
matrix receipt, retained kernel, or image was produced, and QEMU attempts were
zero. Evidence is retained at:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/arm64-real-el0-20260812T-live4/
```

No shared-storage cleanup or retry was performed. Live validation of the root
nonce repair remains pending after host build/cache storage is safely freed or
relocated to the configured big-storage root.

The canonical rebuild wrapper now routes per-row native cache, explicit kernel
output, temporary files, filesystem payload intermediates, and disk image to
the configured big-storage build-cache tree. Only validated `build/os` symlinks
are atomically published, with target-containment and hostile-temp-symlink
self-tests. This is source/static evidence only; no cleanup, rebuild, or QEMU
run accompanied the routing change.

## Big-storage live5 result and exact-text blocker

The next sole construction completed with all large mutable paths under
`/mnt/data/.simple/qemu/build-cache/arm64-live5`; repo-facing kernel/image paths
were validated symlinks, and no fresh object files appeared in repo source or
build trees. Nonce preparation and static gates passed. Exactly one TCG boot
retained at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-real-el0-20260812T-live5/`
again reached VFS ready.

The nonce path now prints as the exact canonical `/QEMUNONC.TXT` and no longer
enters the SYS/APPS trace. However, it also fails to enter the exact root branch
(trace 240 is absent) and returns zero bytes. This narrows the next source task
to ARM64 text equality/match lowering for the canonical path; use an explicit
byte/length predicate or compiler fix rather than another alias/fallback.
Serial SHA-256 is
`d8a01ace56a113aee455b2986717c00b158a999eb81cec74f068d5d3a205343b`.
Nonce, listing, EL0 stdout, exit 37, resume/reap, and TEST PASSED remain absent.

The route now uses a typed freestanding C classifier with exact runtime-string
length/byte comparisons and closed raw codes; the Simple route no longer uses
text equality, match, or prefix lowering. Its executable C regression rejects
near-case, trailing, embedded-NUL, alias-shaped, directory-only, and unknown
paths while accepting the four exact root files and populated SYS/APPS/SYS
descendants. The compiler defect is tracked separately in
`arm64_freestanding_text_equality_route_miscompile_2026-08-12.md`. No rebuild
or QEMU run accompanied this source repair.
