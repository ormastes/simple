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
