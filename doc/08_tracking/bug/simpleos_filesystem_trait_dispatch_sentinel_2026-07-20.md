# SimpleOS hosted FileSystem-layer trait dispatch still sentinels (ud2) after C8 BlockDevice fix

- **ID:** simpleos_filesystem_trait_dispatch_sentinel_2026-07-20
- **Status:** OPEN
- **Severity:** high (blocks enabling the hosted FAT32 mount / app-surface
  materialization on evidence boots)
- **Found by:** BROWSER-FS lane, 2026-07-20
- **Related (SEPARATE, now RESOLVED):**
  doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md
  (C8 BlockDevice-dispatch = fixed by current seed — see below)
- **Related:** browser_demo_frozen_loading_placeholder_2026-07-12.md,
  simple_web_readiness_marker_aspirational_diskless_2026-07-20.md

## Summary

Two distinct trait-dispatch codegen behaviors in the freestanding
`--entry-closure --opt-level=aggressive --target x86_64-unknown-none` kernel:

1. **BlockDevice dispatch — FIXED in the current seed.** `read_sector`/
   `write_sector`/`sector_size` on the `BlockDevice` trait now lower to REAL
   vtable slots (0 / 1 / 2). Verified with `SIMPLE_DEBUG_METHOD_DISPATCH=1`:
   `'sector_size' lowered as virtual trait call at slot 2` (was
   `4294967295` = `DUCK_DISPATCH_UNSUPPORTED_SLOT` in the stale 2026-07-11
   seed). This is the original C8 `blockdevice-dispatch-codegen-bug`, and it
   is RESOLVED — the hosted `Fat32Core.mount()` now succeeds end-to-end
   (evidence below, ladder rung (a)).

2. **FileSystem-layer trait dispatch — STILL sentinels (this bug).** The
   `open` / `stat` / `read` (and the internal dispatch inside
   `Fat32Core.read_dir_entries`) methods STILL lower to
   `DUCK_DISPATCH_UNSUPPORTED_SLOT` (`4294967295`). At runtime the sentinel
   emits `mov $stub,%eax; call *%eax; ud2` (a diagnostic print + `#UD` trap).
   Because the freestanding fault handler does a blind `RIP += 2` recovery on
   any vector (including `#UD`), execution free-runs into adjacent code and
   the desktop never renders (black screen).

## Evidence (this lane)

Scratch build: FIXED seed `scratchpad/seeduntag_backup/simple.FIXED`, C8
skip lifted (`vfs_boot_init.spl:375` `if true:` -> `if false:`), booted under
QEMU q35 + NVMe FAT32 disk (`scratchpad/browserfs_boot.sh`).

- Serial (rung a): `[vfs-init] hosted fat32 mount ENABLED` ->
  `[vfs-init] shared FAT32 root mounted after direct bootstrap` ->
  `[vfs-init] required desktop app payloads cached` ->
  `[vfs-init] executable load probe ok path=/sys/apps/browser_demo.smf bytes=4096`
  -> `[vfs] mounted fat32 provider=pure-simple-direct` ->
  `[vfs-init] VFS ready (pure-Simple NVMe + FAT32)`. Mount verified working.
- Then, during the desktop font read (`gui_entry_desktop.spl:393`
  `g_vfs_read_file_bytes("/"+font_path)`), a single fault:
  `rip=0x08c08573 cr2=0x0`, backtrace `ra=Fat32Core.read_dir_entries+0x1a59`.
  Disassembly at the fault RIP:
  `8c0856f: mov $0x8010dc0,%eax; ff d0 call *%eax; 0f 0b ud2` — the exact
  `DUCK_DISPATCH_UNSUPPORTED_SLOT` sentinel stub. (`Color.to_u32` is only the
  nearest-preceding symbol; the stub is an unnamed region after it.)
- `SIMPLE_DEBUG_METHOD_DISPATCH=1` build log: `'open'/'stat'/'read'` all
  `lowered as virtual trait call at slot 4294967295` (46 sentinel sites total,
  all FileSystem/VfsNode-layer + a few render-loop methods
  `frame_for_time`/`next_frame_due_micros`), while `read_sector`/`write_sector`/
  `sector_size` resolve to real slots in the same build.

## Root-cause hypothesis (discriminator)

BlockDevice methods resolve; FileSystem-trait methods don't — under an erased
receiver (`[MIR-METHOD-DISPATCH] bare 'stat' call: receiver ty = Any`). Likely
`find_trait_for_method_on_receiver`
(`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`) resolves
`sector_size` (unique to one trait) but not `stat`/`open`/`read` (names shared
across several traits, or the FS trait's impl not found in the dependency
graph for an erased receiver). This is a language/compiler resolution limit,
NOT a stale-seed miss — it reproduces under `simple.FIXED`. It is the same
CLASS as C8 (the `DUCK_DISPATCH_UNSUPPORTED_SLOT` guard misfiring for a real,
present impl) but a DIFFERENT dispatch site than the fixed BlockDevice one.

Also flagged (separate, real): the freestanding fault handler treating a
compiler-emitted `#UD` (ud2) trap as a recoverable `RIP+=2` event is wrong — a
`ud2` should park/terminate, not "recover" into adjacent code. (Same note as
the C8-FIX addendum in the 07-17 doc.)

## Impact on enabling the hosted mount

Lifting the C8 skip lets `Fat32Core.mount()` succeed AND caches the app
payloads (needed for browser_demo to materialize), but sets
`g_vfs_initialized=true`, which routes any file NOT served by the direct
scalar reader / app-registry cache into the hosted `g_root_fat32` path
(`vfs_init.spl:g_vfs_read_file_bytes`), where it hits the sentinel above. On a
pure-Simple boot the direct scalar reader + cache are authoritative, so the
intended workaround is to keep `g_vfs_read_file_bytes` on the direct/cache path
and never enter the hosted trait path.

## Workaround attempt (correct in source, did NOT reach the binary — build-infra blocker)

Intended interim fix: guard `g_vfs_read_file_bytes` to `return []` when
`vfs_boot_storage_is_pure_simple()` is true, so pure-Simple boots never enter
the hosted trait path. This is source-correct (on a pure-Simple boot the
direct reader + cache already serve every needed file, so it changes no
observable read behavior) but it **never reached the compiled kernel**:

- The compiled `g_vfs_read_file_bytes` was byte-identical (16876704-byte ELF)
  WITH and WITHOUT the edit — no reference to the `g_vfs_boot_storage_pure_simple`
  global (0x…bea0), only `g_vfs_initialized` (0x…bea8).
- Decisive test: a `serial_println("…BFS_GUARD_20260720")` placed inside the
  new guard branch (a side-effecting call that CANNOT be dead-code-eliminated)
  did **not** appear anywhere in the ELF (`strings`/raw grep = 0). So the
  function is not being recompiled from the edited source — this is NOT
  "compiled then optimized out" (an earlier const-fold hypothesis, now
  disproven by the marker test).
- Not a `--cache-dir` staleness issue: reproduced with a pristine, never-used
  `--cache-dir` and `touch`-ed sources. `build/native_cache/` (the global
  incremental cache) has an EMPTY cranelift/opt3 entry and its manifest holds
  only unrelated single-file probes — so it is not the object source either.
- **Asymmetry:** an edit to the SAME-directory `vfs_boot_init.spl` (the skip
  lift, a unique `serial_println` string) DID compile and appear at runtime,
  while every `vfs_init.spl` edit was ignored. The compiler opens the correct
  on-disk file (verified: no symlinks, mtime/size reflect the edit).

Leading hypothesis: **shadow-source / duplicate-module resolution.** Two other
checkouts contain the same module path —
`build/worktrees/simpleos-sync-recover-gh/src/os/services/vfs/vfs_init.spl` and
`build/worktrees/pure-simple-tool-remain/src/os/services/vfs/vfs_init.spl`
(both pre-date the edit). If native-build's module discovery indexes the
project tree (not only the explicit `--source` roots) it may bind
`services.vfs.vfs_init` to a worktree copy, silently ignoring the edited
`src/os/...` file. This is a THIRD, separate issue (build/module-resolution),
and it is what blocked verifying the interim fix. Needs its own investigation
(confirm by temporarily relocating the worktree copies, out of scope here to
avoid disturbing concurrent sessions).

Robust interim fix once the shadow-source issue is resolved: the guard above,
OR fix the FileSystem-trait dispatch resolution itself (preferred).

## Fix direction

1. Extend the `find_trait_for_method_on_receiver` fix (that resolved
   BlockDevice) to FileSystem-layer traits under erased receivers, so
   `stat`/`open`/`read` lower to real slots.
2. OR make `#UD` non-recoverable in the freestanding fault handler.
3. Interim: robustly gate `g_vfs_read_file_bytes` off the hosted trait path
   for pure-Simple boots (workaround above, once the const-fold issue is
   addressed).
