# `llvm-sys` pinned to 18.x blocks using the newest MSVC-built LLVM (OPEN, scoped)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Date: 2026-08-09
Area: Windows Rust-seed build toolchain, `llvm-sys`/`inkwell` dependency

## Summary

The goal asked for "most recent llvm of msvc" to be installed and wired in.
LLVM 21.1.3 (MSVC build) was downloaded to this host, but the Rust seed's
`llvm-sys` crate dependency is pinned to version `180.0.0`, which hard-requires
an LLVM 18.x `llvm-config`/library set — it will not link against LLVM 19, 20,
or 21. The Windows Rust-seed bootstrap this session was therefore wired against
the already-present LLVM 18.1.8 MSVC build
(`C:/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc`, forced via
`LLVM_SYS_180_PREFIX` to defeat PATH-order contamination from a MinGW
`llvm-config` — see
`directx_windows_probe_and_rust_seed_rebuild_chain_2026-08-09.md` item #2),
**not** the newer 21.1.3 install, and the full Windows bootstrap
(`cargo build --profile bootstrap -p simple-driver --bin simple --features
llvm`) now succeeds end-to-end on that 18.1.8 pin.

## Why this wasn't bumped this session

Moving to LLVM 21 requires bumping `llvm-sys` (and very likely `inkwell`, which
tracks `llvm-sys` major versions) across the whole `compiler_rust` workspace —
a real dependency-version migration that can change API surface used by the
LLVM backend codegen path, not a flag or env var change. That is out of scope
for a same-session fix alongside the rest of the Windows bootstrap-blocker
chain; attempting it blind risked trading a working, verified LLVM-18 bootstrap
for an unverified, possibly-broken LLVM-21 one.

## What's left

- Evaluate `llvm-sys`/`inkwell` versions that support LLVM 19/20/21 (check both
  crates' changelogs for the version pinned to each LLVM major).
- Bump the dependency, fix any resulting compile errors in the LLVM backend
  (`src/compiler_rust/compiler/src/**llvm**`), and re-run the full T3 bootstrap
  (`.claude/rules/bootstrap.md`) on all three supported host platforms, not
  just Windows.
- Re-point `LLVM_SYS_180_PREFIX`-style env plumbing at whatever versioned env
  var the new `llvm-sys` release expects.
- Keep the 18.1.8 install around as a fallback until the 21.x path is verified
  green, since the current bootstrap depends on it.

## Current state

Not a blocker for anything the goal required this session (Windows bootstrap,
DirectX/Windows-only tests) — LLVM 18.1.8 is a real, currently-supported,
recent-enough MSVC LLVM build and the bootstrap it produces is fully verified
(see `directx_windows_probe_and_rust_seed_rebuild_chain_2026-08-09.md`).
Recording this as a separate, explicitly scoped follow-up rather than silently
treating "most recent LLVM" as satisfied by the 18.x pin.

## Re-verified 2026-08-17 (worker s3_rust_other) — LIVE, pin located

The pin the doc could not previously locate is indirect, which is why a
`grep llvm-sys` on `compiler/Cargo.toml` found nothing:
`src/compiler_rust/compiler/Cargo.toml:105` —
`inkwell = { version = "0.5", optional = true, features = ["llvm18-0"] }`,
enabled by `:18` `llvm = ["inkwell"]`. That feature maps to `llvm-sys-180`
(`src/compiler_rust/vendor/inkwell/Cargo.toml:78-81`) and the vendored crate is
`version = "180.0.0"` (`src/compiler_rust/vendor/llvm-sys/Cargo.toml:14`). No
19/20/21 option is wired anywhere. Pin confirmed at 18.x.

## Content re-verification 2026-08-17 (m2_rust_compiler lane) — pin located, OUT OF SCOPE

The pin is not in `src/compiler_rust/compiler/Cargo.toml` (zero `llvm-sys` hits there,
which is why triage could not confirm it). `llvm-sys` is **vendored**:
`src/compiler_rust/vendor/llvm-sys/Cargo.toml`, reached via
`src/compiler_rust/vendor/inkwell`, and recorded in `src/compiler_rust/Cargo.lock:2375`.
`src/compiler_rust/vendor/**` is excluded third-party source under CLAUDE.md's
Owned-Code Scope, so this row is not actionable from the compiler crate and is
an environment/toolchain constraint rather than a silent-wrong-result defect.
