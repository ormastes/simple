# main unbuildable on macOS aarch64: metal_impl gated on OS but deps gated on feature (2026-08-31)

**Status: FIXED** (this commit)

## Evidence
CI job 99376080213, workflow "Rust Bootstrap Multiplatform", macOS aarch64 native job,
step `Build`, on the tip of PR #148 (which touches ZERO Rust files — pre-existing
`main` breakage):

```
error[E0432]: unresolved import `objc2_metal`
error[E0432]: unresolved import `dispatch2`
Some errors have detailed explanations: E0432, E0433.
error: could not compile `simple-runtime` (lib) due to 5 previous errors
```

## Root cause
`src/compiler_rust/runtime/src/metal_graphics_runtime.rs` gated its real Metal
implementation (`mod metal_impl` and ~65 dispatch sites) on
`#[cfg(target_os = "macos")]` only, but the crates it imports (`objc2`,
`objc2-foundation`, `objc2-metal`, `dispatch2`) are **optional** dependencies in
`runtime/Cargo.toml`, enabled only by the non-default `metal` feature
(`default = ["cpu-simd"]`). Any macOS build without `--features metal` — which is
what CI runs — compiled the module body with none of those crates present:
E0432 on each `use`, E0433 on paths. Linux never saw it because Linux takes the
`not(macos)` stub branch; the seed-build guard compiles the host target only.

## Fix
Re-gated the whole file: every `#[cfg(target_os = "macos")]` →
`#[cfg(all(target_os = "macos", feature = "metal"))]`, and every
`#[cfg(not(target_os = "macos"))]` → `#[cfg(not(all(...)))]` (69 sites).
macOS-without-metal now compiles the exact stub branch Linux already compiles.
No functionality deleted: `--features metal` on macOS still builds the real
backend, matching the existing `cfg!(all(target_os = "macos", feature = "metal"))`
runtime dispatch in `runtime/src/lib.rs:76`.

## Verification (Linux host — no macOS compile was performed)
- `cargo check --release --bin simple`: PASS (no host regression).
- `cargo check --release -p simple-runtime --features metal` on Linux: PASS
  (feature on, cfg off — proves feature wiring is sound).
- `cargo check --target aarch64-apple-darwin` (rust-std installed via rustup):
  stopped in vendored `ring`'s C build script (needs an Apple `cc`/SDK) before
  reaching simple-runtime's Rust type-check — expected cross-limit, reported
  honestly. What IS proven by construction: the failing imports now sit inside a
  cfg branch that is off on a default macOS build, and the branch that build
  takes is token-identical to the Linux-compiled stub branch.
- UNPROVEN without a Mac: the `--features metal` macOS path (unchanged content,
  same status as before this bug).

## Guard gap
`scripts/check/check-seed-builds-push.shs` runs `cargo check` for the HOST
target only, so a macOS-only cfg breakage sails through — exactly the fail-open
class its 2026-08-18 rework closed for docs-only pushes, now on the target axis.
A cheap partial close is feasible: `rustup target add aarch64-apple-darwin` +
`cargo check -p simple-runtime --target aarch64-apple-darwin` type-checks the
macOS cfg paths of pure-Rust crates, but the workspace pulls vendored C
(`ring`) whose build script needs an Apple toolchain, so a full-workspace
cross-check ERRORs on this host. Left as a filed gap rather than a weakened or
half-wired guard; closing it needs either stubbing ring out of the check lane
or a macOS CI-side required check.
