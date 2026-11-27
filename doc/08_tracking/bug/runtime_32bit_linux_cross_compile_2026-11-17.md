# simple-runtime cross-compile failed on 32-bit Linux (i686, armv7)

Status: verification-pending
Date: 2026-11-17

## Symptom
Cross-compile matrix phase-2 at b45dd8065b5: `could not compile simple-runtime`,
19 errors on linux-i686, 18 on linux-armv7.

## Cause and fix
Fixed by 7f6b761eb44 (already on release/1.0.0 before this lane started):
64-bit width assumptions for st_size/st_ino/off_t/rlim_t (now libc widths,
try_from narrowing, saturating rlimits), socketcall(2) deny on i386, and
direct-function records read as two u64 slots. Pin:
`scripts/check/check-runtime-32bit-cargo-check.shs`.

## Re-verification (Windows host, nightly-2026-09-15, 8d37cf1f31d)
- `cargo check -p simple-runtime --target i686-unknown-linux-gnu`: 0 errors
- `cargo check -p simple-runtime --target armv7-unknown-linux-gnueabihf`: 0 errors
- same with `--lib --tests` in `runtime/`: 0 errors on both targets
- C build scripts (ring, libmimalloc-sys) were stubbed with a no-op CC/AR, since
  no Linux sysroot exists on the host; `cargo check` does not use their output.
  The pin script itself (clang) needs a sysroot and was not run here.

## Remaining
- Matrix lane (`simple-native-all --features driver-compat`, bootstrap profile)
  not re-run on this host; verification-pending until the next matrix run.
- Unrelated: `runtime/src/value/pty.rs:1564-1584` test code uses unix-only libc
  items and fails `cargo check --tests` on x86_64-pc-windows-msvc (8 errors).
