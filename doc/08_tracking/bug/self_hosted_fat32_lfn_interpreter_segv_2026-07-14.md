# BUG: self-hosted runner segfaults on focused FAT32 LFN interpreter spec

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
