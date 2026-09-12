# Release: Linux→Windows-gnu cross seed build broken (2026-07-17)
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Lane:** release.yml `build-bootstrap` windows-x86_64 cross (Linux runner,
`cargo build --profile bootstrap -p simple-driver --target x86_64-pc-windows-gnu`).
Cargo uses vendored sources (`replace-with = "vendored-sources"`), so CI fails
identically to local.

## Defects found (release sanity 2026-07-17)

1. **`src/runtime/runtime_hosted_signal.c` POSIX-only** — added 2026-07-17 by
   `42d0c8694df` (mac Stage4 memory fix); uses `sigaction`/`SA_RESTART` with no
   `_WIN32` guard while `runtime/build.rs` compiles it unconditionally.
   **FIXED in WC:** `#ifdef _WIN32` path using C-standard `signal()`; verified
   with `x86_64-w64-mingw32-gcc -c -Wall -Werror` and native cc.

2. **Vendored windows-gnu import libraries stripped** — three vendor crates had
   their `lib/*.a` removed and `.cargo-checksum.json` regenerated without them,
   breaking the final links (`cannot find -lwindows.0.52.0`, `-lwinapi_*`,
   `-lwindows.0.48.5`):
   - `vendor/windows_x86_64_gnu-0.52.6/lib/` (its `libwindows.0.52.0.a` was
     sitting misplaced-but-git-tracked in unversioned
     `vendor/windows_x86_64_gnu/lib/` since Jul 1)
   - `vendor/winapi-x86_64-pc-windows-gnu/lib/` (1416 files, ~54 MB)
   - `vendor/windows_x86_64_gnu-0.48.5/lib/` (~12 MB)
   **RESTORED in WC** from pristine crates.io crates (cargo fetch, checksums
   from lock resolution). Note `vendor/windows_x86_64_gnullvm-0.52.6/lib` was
   never stripped — repo convention tracks these libs; the strip was partial
   and silent.

## Verification

After both fixes: `XWIN4_EXIT=0`, artifact
`target/x86_64-pc-windows-gnu/bootstrap/simple.exe` = PE32+ console x86-64,
24.2 MB. Logs: session scratchpad `xwin-rebuild{,2,3,4}.log`.

## Remaining decision

Committing the restored libs adds ~79 MB of binary blobs (per-file well under
GitHub's 100 MB limit; same class as already-tracked gnullvm libs). Alternatives
if size is unacceptable: fetch these three crates non-vendored in the windows
cross lane, or move the windows crate to `windows_raw_dylib`. Until one lands,
the CI windows-gnu cross lane stays red.

## Status (2026-07-18)

FIXED+PUSHED at 310bcdf1131. Both defects resolved: signal.c _WIN32 guard + restored vendor libs (79 MB size decision accepted by commit). Cross-build verified: PE32+ simple.exe produced locally.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
