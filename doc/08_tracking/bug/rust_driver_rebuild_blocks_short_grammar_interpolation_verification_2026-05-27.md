## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Resolved in local worktree

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Rust driver rebuild blocked short grammar interpolation verification

Date: 2026-05-27
Status: Resolved in local worktree

## Summary

Short-grammar placeholder support for string interpolation initially could be verified only in the Rust parser crate because the end-to-end `simple` CLI could not be rebuilt in this workspace.

## Evidence

- `cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-parser` passes.
- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-parser --test expression_tests` passes, including `test_map_placeholder_inside_fstring_interpolation`.
- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-parser --lib` now passes after replacing the stale `include_str!` fixture with an inline representative source.
- `cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver` now passes.
- `cargo build --manifest-path src/compiler_rust/Cargo.toml --bin simple` now passes.

## Root Cause

The runtime build script generated symbol-table entries for plain Rust helper functions and feature-gated regex exports by scanning for `fn <symbol>` anywhere in runtime sources. That created unresolved C symbol references when `runtime-regex` was disabled.

## Fix

The build script now only treats Rust functions as runtime exports when they have a nearby `#[no_mangle]` or exact `#[export_name = "..."]`, and it skips `regex.rs` when the `runtime-regex` feature is disabled.
