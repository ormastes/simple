# BS5 Rust Dependency Trim Receipt — 2026-09-02

## Scope

- Audited `src/compiler_rust/loader/Cargo.toml`, `src/compiler_rust/native_loader/Cargo.toml`, and `src/compiler_rust/native_all/Cargo.toml`.
- Audited their owned Rust source, tests, target-feature edges, loader-driver consumers, and native-all aggregate exports.
- Excluded vendored crates and unrelated workspace manifests.

## Decision

- Removed: `cc = "1"` from `simple-native-loader` dev-dependencies.
- Evidence: native-loader tests invoke the external `cc` executable through `std::process::Command`; owned source and tests contain no `cc::` Rust API reference.
- Preserved bootstrap authority: yes.
- Preserved all loader, runtime ABI, SIMD, platform loading, native-all, hosted-runtime, and optional driver-compat dependencies because owned code or the feature graph references them.
- No source files, lockfile entries, vendored crates, target features, or transitive dependencies were removed.

## Static Authority

- `scripts/check/check-bs5-rust-dependency-trim.shs` rejects restoration of the unused direct dependency, a new `cc::` reference without manifest authority, removal of required loader/native-all dependencies, feature-edge drift, or a stale receipt.
- `test/01_unit/scripts/bs5_rust_dependency_trim_test.shs` executes the focused checker without compiling the workspace.

## Result

One direct dependency was removed. No other dependency had sufficient owned-code and feature-graph evidence for conservative removal.
