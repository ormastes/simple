# BUG: self-hosted runner segfaults on focused FAT32 LFN interpreter spec
## Open 2026-09-16 — triaged 2026-11-25: not reproducible on this host; remains open pending a Linux self-hosted rerun (see triage note at bottom)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** open
**Severity:** high (blocks pure-Simple verification)
**Component:** self-hosted `simple test` runtime
**Found:** 2026-07-14

## Symptom

The isolated FAT32 LFN worktree has no `bin/simple`. A cached self-hosted
release executable identifies itself as `Simple v1.0.0-beta`, but the focused
interpreter command exits with signal 11 (status 139) and emits no diagnostics.

## Reproduction

From `/tmp/simple-fat32-lfn-20260714`:

```bash
env SIMPLE_LIB=src \
  /home/ormastes/dev/pub/simple/build/worktrees/simpleos-sync-recover/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl \
  --mode=interpreter --clean
```

Observed: exit 139, empty stdout/stderr. The command was attempted once. The
Rust bootstrap seed was not used as fallback.

## Required fix

Reproduce with a current pure-Simple self-hosted build, retain a crash trace,
and fix the runner/runtime fault before accepting this spec as executed release
evidence.


## Triage 2026-11-25 (release/1.0.0 HEAD 4bc2c986375, work/p2w5-aa lane)

Not closable and not fixable from this environment:

- The crash was a SIGSEGV (exit 139) in a **cached Linux self-hosted binary**
  (`Simple v1.0.0-beta`) in an isolated worktree that had no `bin/simple`.
  This host is Windows and has only the pinned tracked v1.0.0-rc.1 Rust seed
  at `bin/simple.exe`; no pure-Simple self-hosted binary exists here and
  building one (bootstrap) is out of scope for this lane.
- Running the named spec with the pinned seed is environment-blocked:
  `bin/simple.exe test test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl
  --mode=interpreter` fails at semantic analysis with
  `unknown decorator '@representation_boundary'` (the known
  source/binary inconsistency at release/1.0.0 HEAD — commit cfd89933699's
  940 annotations vs. the pinned rc.1 seed), before the spec can load. This
  is a harness limitation, not evidence about the segfault.
- The spec itself still exists unchanged in scope
  (`test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl`).

The "Required fix" stands as written: reproduce with a current pure-Simple
self-hosted build on Linux, retain a crash trace, and fix the runner/runtime
fault. Status stays **open**; this note only records that the 2026-11-25
sweep could not advance it from a Windows seed-only host.
