# Windows gnu lane (MinGW UCRT) bootstrap blockers (2026-10-24)

Observed while running `bootstrap-from-scratch.sh --full-bootstrap
--stop-after-stage2 --produce-managed-receipt=release-trust-verification
--jobs=full --jobs-memory-policy=explicit-count` on
`origin/release/1.0.0 @ 15b6eb702a13` (worktree, clean tree).

The env script (`scripts/setup/windows-gitbash-bootstrap-env.shs`) now
defaults the Windows lane to MinGW UCRT (`SIMPLE_WINDOWS_ABI:-gnu`; MSVC is
opt-in via `SIMPLE_WINDOWS_ABI=msvc`). Three blockers in the fresh gnu lane:

## 1. Custom Rust target `x86_64-pc-windows-gnullvm` has no installed std

`scripts/setup/platform-detect.shs:60` maps the gnu platform to a custom
triple `x86_64-pc-windows-gnullvm` (gnu ABI + LLVM compiler-rt/libunwind, no
libgcc). The seed cargo build then fails:

```
error[E0463]: can't find crate for `core`
  = note: the `x86_64-pc-windows-gnullvm` target may not be installed
  = help: consider downloading the target with `rustup target add ...`
  = help: consider building the standard library from source with `cargo build -Zbuild-std`
```

`rustup target add` cannot fetch this custom triple; the lane must either
ship a target spec json + `-Zbuild-std` on the nightly toolchain, or install
a prepared std. Until then the gnu lane cannot build the seed.

## 2. LLVM 23 root is dropped by the bootstrap env scrub

With the gnu lane, platform detection reports
`error: admitted LLVM 23 (any 23.x.y) not found (shared platform detection:
scripts/setup/platform-detect.shs, versions: 23)` even though
`config/host/DESKTOP-VMF96U6.sdn` records
`llvm_root: /c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc` (a valid
LLVM 23 with bin/LLVM-C.dll + llvm-config; `host-env.shs --get llvm_root`
returns it). Exporting `LLVM_SYS_231_PREFIX`, `SIMPLE_LLVM_ROOT`, or
`SIMPLE_HOST_LLVM_ROOT` does NOT survive the bootstrap's environment scrub /
re-exec, so the detection fallback (PATH llvm-config scan) binds the
llvm-mingw toolchain's LLVM or none. The scrub's whitelist carries
`SIMPLE_MINGW_ROOT` but no LLVM-root variable.

## 3. `lld-link.exe` on the env-provided PATH fails with 0xC0000135

The seed build's host build-scripts link through `lld-link`, which fails
with `0xc0000135` (DLL not found). The env script's LLVM-bin selection
(`SIMPLE_LLVM_BIN` discovery under /c/dev/install/clang+llvm-*) bound an
lld-link whose dependencies do not load in the scrubbed environment.

## Workaround in use

Run the lane with `SIMPLE_WINDOWS_ABI=msvc` (explicitly supported opt-in)
which restores the previously-working MSVC platform path; combined with the
interpreter-safe headroom probes (PR #4304) this gets past the earlier
preflight `available: 0 via unknown` admission abort.
