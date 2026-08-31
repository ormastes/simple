# macOS Rust seed unbuildable: Metal module gated on target_os only, not the `metal` feature

Status: RESOLVED (2026-08-30)
Area: runtime / bootstrap / macOS
Severity: blocker — no macOS bootstrap of any kind could start

## Symptom

On macOS (aarch64-apple-darwin), the first step of the sanctioned bootstrap

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
```

fails immediately after `Building Rust seed compiler + runtime library...`:

```
error: rust-seed-build failed with exit 101
error: could not compile `simple-runtime` (lib) due to 73 previous errors
```

All 73 errors are in one file, `src/compiler_rust/runtime/src/metal_graphics_runtime.rs`:

```
error[E0432]: unresolved import `dispatch2`
error[E0432]: unresolved import `objc2_foundation`
error[E0432]: unresolved import `objc2_metal`
error[E0433]: failed to resolve: use of unresolved module or unlinked crate `objc2`
error[E0282]: type annotations needed        (cascade from the above)
```

## Root cause

`4b2ea44ea3a` — *"feat(gpu): isolate backend provider feature builds"* (2026-08-25)
— made the Objective-C bridge crates **optional**, behind a **non-default** cargo
feature:

- `runtime/Cargo.toml:30` — `metal = ["dep:dispatch2", "dep:objc2", "dep:objc2-foundation", "dep:objc2-metal"]`
- `runtime/Cargo.toml:139-143` — all four declared `optional = true`
- `runtime/Cargo.toml:19` — `default = ["cpu-simd"]`, so `metal` is OFF by default

and taught the crate to report the capability accordingly:

- `runtime/src/lib.rs:76` — `if cfg!(all(target_os = "macos", feature = "metal"))`

It did **not** update the module that actually uses those crates.
`runtime/src/metal_graphics_runtime.rs` kept all **69** of its cfg attributes
gated on the platform alone — `#[cfg(target_os = "macos")]` (35 sites) and
`#[cfg(not(target_os = "macos"))]` (34 sites) — including the `mod metal_impl`
declaration at `:21` that carries the `use objc2::…` imports.

Consequence: on any Mac, with the feature off, `mod metal_impl` is compiled
while the crates it imports are not linked into the build graph. The file had
therefore **never** compiled on macOS since 2026-08-25 in any default build.

This is not bootstrap-specific. The same predicate breaks:

- `cargo build -p simple-runtime --features runtime-symbol-table`
  (`scripts/bootstrap/bootstrap-from-scratch.sh:1816`) — the seed build
- `cargo check --release --bin simple` — what
  `scripts/check/check-seed-builds-push.shs` runs

Non-macOS hosts are unaffected: there `#[cfg(not(target_os = "macos"))]` selects
the stub arms and the objc2 imports are never reached. That is why this survived
in `main` — the guard that exists for exactly this class of defect is not wired
into the push path (see `.claude/rules/vcs.md`, "NOT enforced on any push"), and
the Linux lanes are green.

## Fix

Gate the module on the same predicate the crate already uses to report the
capability:

- `#[cfg(target_os = "macos")]` -> `#[cfg(all(target_os = "macos", feature = "metal"))]`
- `#[cfg(not(target_os = "macos"))]` -> `#[cfg(not(all(target_os = "macos", feature = "metal")))]`

69 sites in `runtime/src/metal_graphics_runtime.rs`; the single `#[cfg(test)]`
is untouched.

Without the feature, macOS now takes the **existing stub arms**. This is honest
rather than a silent fake: `lib.rs:76` keys the capability report off the
identical predicate, so the runtime states that Metal is unavailable instead of
claiming a backend it does not have. Real Metal on macOS still builds with
`--features metal`, and the vendored crates (`vendor/objc2`, `vendor/objc2-metal`,
`vendor/objc2-foundation`, `vendor/dispatch2`) are all present, so that build
works offline.

## Verification

```
cargo check --target aarch64-apple-darwin -p simple-runtime --features runtime-symbol-table
Finished `dev` profile ... in 22.10s        # 0 errors, was 73
```

## Deliberately NOT done here

Wiring `--features metal` into the bootstrap's cargo invocation. That is a
separate behavioral decision — previously deployed macOS seeds had live Metal —
and feature unification across the `-p` flags of a single `cargo build` can
ripple into the other provider features (`vulkan`, `cuda`, `pytorch`). It is
irrelevant to getting a macOS seed to build at all, which is what this record
covers. If macOS is meant to ship real Metal by default, that belongs in its own
change with its own gate.

## Follow-up worth filing separately

`check-seed-builds-push.shs` exists and would have caught this, but is in no
push-tier row of `config/check/must_check_gates.sdn`, so nothing runs it on a
push. Its blocker is a warm `CARGO_TARGET_DIR` plus a 1-2 min budget on the
pushing machine. Note also that the guard is host-shaped: a Linux pusher running
it would still have passed this, because the defect is macOS-only.
