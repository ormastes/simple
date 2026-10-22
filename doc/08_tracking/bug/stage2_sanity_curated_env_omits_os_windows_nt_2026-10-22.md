# Stage-2 sanity fails SCV admission: curated bootstrap envs omit OS=Windows_NT (2026-10-22)

## Symptom

The stage-2 sanity smoke fails with:

```
workarounds: refresh failed: workaround Git failed (-1):
SCV-E-ADMISSION: git-event-source-unavailable
candidate_frontend_smoke: p2_add-build failed (raw rc=1)
```

## Root cause

`src/lib/nogc_sync_mut/io/process_ops.spl` `_is_windows_platform()` decides
the process-spawn implementation from `env_get("OS")`. The bootstrap's
curated native environments all omitted `OS`:

- `bootstrap_stage_sanity` scrubs the entire environment and re-exports a
  captured allowlist (SystemRoot/SystemDrive/ProgramData/INCLUDE/LIB/...) that
  did not include `OS`.
- the stage-2/stage-3 `native-build` env word lists (and the pre-exec
  canonical allowlist `bootstrap_stage3_stage2_canonical_env_names` in
  `scripts/check/lib/bootstrap-stage3/authority.shs`) likewise omitted it.

Without `OS=Windows_NT`, `_is_windows_platform()` is false, every bare-name
child spawn (`git` above all, also the workaround refresh's git call) takes
the POSIX path, and the spawn fails with -1. The stage-2 *build* survived
only because it spawns tools by absolute path (CC) and runs with SCV
disabled (`SIMPLE_BOOTSTRAP=1`); the sanity (bootstrap=0 pass) exercises real
SCV admission and dies.

Bisection: with the sanity env reduced to `PATH HOME TMPDIR TEMP TMP LC_ALL
LANG + <candidate var>`, `OS` alone flipped the p2_add smoke from
git-event-source-unavailable to proceeding past admission.

## Fix

- `scripts/bootstrap/bootstrap-from-scratch.sh`: add
  `bootstrap_windows_os_env="OS=${OS:-Windows_NT}"` on windows and emit it in
  the stage-2/stage-3 native-build env lists; capture and re-export `OS` in
  `bootstrap_stage_sanity`.
- `scripts/check/lib/bootstrap-stage3/authority.shs`: add `OS` to
  `bootstrap_stage3_stage2_canonical_env_names` for both `*windows-gnu*` and
  `*windows-msvc*` (pre-exec env-name guard).

A first attempt converted the sanity PATH to Windows form (`cygpath -pw`) to
fix `git` resolution; that proved unnecessary (native spawning resolves git
through the POSIX PATH fine once `OS` is present) and broke the sanity
subshell's own MSYS tooling (`dirname`/`awk`/`openssl`: command not found),
so it was reverted.

## Follow-ups observed (not yet fixed)

- With admission unblocked, the smoke's p2_add fixture build on the **llvm**
  backend exceeded the 180 s `COMPILER_BUILD_TIMEOUT_SECONDS` (raw 124); a
  manual llvm-backend fixture build did not finish in >6 minutes while the
  cranelift path completes in seconds. Frontend smoke backend selection uses
  `${backend}` whenever llvm features are present
  (`bootstrap-from-scratch.sh` ~line 2039); investigate the llvm-backend
  fixed cost or bound it separately from the frontend gate.
- The workaround refresh reports `canonical bug database CRC mismatch` on
  this checkout even though the raw-byte CRC of
  `doc/08_tracking/bug/bug_db.sdn` matches its header (verified with
  zlib.crc32). Likely a `crc32_text` text-re-encode divergence on some byte
  sequence in the body; previously masked by the WAL guard firing first.

## Evidence

- 2026-10-22, `release_phase3`: sanity failed with git-event-source-unavailable
  in three consecutive full-bootstrap attempts; after the OS fix, admission
  proceeds (next failure is the unrelated llvm timeout above).
