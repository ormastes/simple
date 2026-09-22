# Bootstrap LLVM 23.1 toolchain pins

The macOS bootstrap compiler authority now honors `CC` and requires a Clang
version response. Explicit GCC/G++ compiler names are rejected. Hermetic Cargo
calls forward CXX, AR, LD, LLVM_CONFIG, the ARM macOS linker, and ARM macOS Rust
flags. RUSTFLAGS supplies the macOS target flags when no target override exists;
this preserves the Windows GNU target flag policy. Forwarded settings enter the
seed fingerprint so a changed pin cannot reuse an old authority silently.

## Verification

- `sh scripts/check/check-bootstrap-cargo-toolchain-pins.shs`: PASS. Real shell
  execution covers four LLVM enabled/disabled and LTO enabled/disabled branches,
  explicit Clang selection, GCC/G++ rejection, and unrelated environment removal.
- Shell syntax and diff whitespace checks: PASS.
- Official Homebrew ARM64 bottles installed without cleanup: LLVM/Clang 23.1.1
  at `/opt/homebrew/Cellar/llvm/23.1.1_1`; LLD 23.1.1 at
  `/opt/homebrew/Cellar/lld/23.1.1`. clang, clang++, llvm-config, llvm-ar,
  and ld64.lld version outputs verified. A C program compiled, linked with
  explicit ld64.lld, and exited successfully.
- Installed Rust nightly reports rustc 1.100.0-nightly, LLVM 23.1.1.

## Resource and SoSIX review

The change adds one bounded compiler version probe at authority resolution.
There is no full-tree scan, cache deletion, build, download, retry, or background
worker in the new contract check. The check uses one temporary directory and
removes only that directory. No shell eval, unquoted compiler execution, or
cross-domain mutable state is introduced. Tool paths remain quoted, including
paths containing spaces. Parent bootstrap continues to own publication and
cache admission; no new producer or output authority exists.

## Compatibility boundary

`--backend=cranelift` leaves `llvm_features` empty. The Rust compiler crate's
`default = []` and driver default allocator feature do not enable optional
Inkwell, so this lane can build without LLVM18 bindings while rustc, C/C++, and
link tools use 23.1.1. A complete producer build remains integrator-owned and has
not been run as part of this contract check.

`--backend=llvm` and `llvm-lib` still enable Inkwell0.5's llvm18-0 feature.
External LLVM23 cannot safely substitute for that ABI. Migration requires
updating Inkwell/llvm-sys, vendored dependencies and checksums, LLVM API call
sites, platform detection defaults and consistency checks, and native runtime
LLVM loading compatibility, followed by backend correctness and bootstrap
verification. This change does not claim that migration.

## Focused baseline/candidate resource profile

Single paired `/usr/bin/time -l` authority selection probe, both resolving the
same pinned Clang23.1.1 (baseline PATH cc shim, candidate explicit CC): baseline
0.01 s / 3,604,480 bytes max RSS; candidate 0.19 s / 32,751,616 bytes max RSS.
The candidate adds a real Clang version validation subprocess; this is a bounded
startup cost, not a compilation throughput measurement. Peak is under 32 MiB,
well below the 6 GiB cap. No complete bootstrap performance claim is made.
Logs: `/tmp/simple-llvm23-toolchain/{base,candidate}-profile.log`.

## Review corrections

Explicit LLVM_CONFIG now selects the binary in both snapshot and seed receipts.
Darwin tool snapshots use the same selected CC as Cargo. Unset CXX/AR/LD remain
unset in hermetic Cargo, preserving Windows target-aware defaults; a contract
case exercises this directly. `SIMPLE_LLVM_REQUIRED_VERSION=23.1.1` enables the
invocation-owned fail-closed gate: CC/CXX/AR/LD/LLVM_CONFIG must be absolute,
executable, and report exactly that version; rustc embedded LLVM must match.
The producer must set this variable; this does not migrate repository-wide
default backend policy. CXX/AR/LD seed fields bind setting strings, not immutable
binary content hashes. Exact versioned Cellar paths are used for this run.

Rust LLVM validation now runs on the repository-policy-resolved compiler in
both resolver paths, not ambient RUSTC. A negative fixture verifies an ambient
override cannot hide a resolved LLVM mismatch. Strict mode requires the
effective Rust linker to equal selected CC, preventing a linker override from
bypassing the compiler pin. Installed resolved nightly Rust passes; an alternate
Apple Clang linker override is rejected.
