# SFFI Bidirectional Interop Completion Report

Date: 2026-03-30
Status: PASS

## Baseline

The requested `doc/03_plan/sffi_bidirectional_interop_completio...` path does not exist in this repository.
Implementation and verification were completed against these repo-tracked artifacts instead:

- `doc/05_design/phase4_sffi_implementation_plan.md`
- `doc/02_requirements/feature/usage/sffi_bidirectional_interop.md`
- `doc/02_requirements/nfr/sffi_bidirectional_interop.md`
- `doc/04_architecture/sffi_bidirectional_interop.md`
- `doc/05_design/sffi_bidirectional_interop.md`

## Implemented

### REQ-SFFI-BIDIR011: Plugin Manifest for Extern Fn Registration

- Added Rust-side plugin manifest loading in `src/compiler_rust/compiler/src/plugin_manifest.rs`
- Integrated manifest-registered extern symbols into interpreter startup in `src/compiler_rust/compiler/src/interpreter_eval.rs`
- Added manifest-first dynamic library resolution and caching in `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs`
- Added Simple-side plugin registry and minimal CLI under `src/app/plugin/`
- Added Rust driver dispatch entries for `simple plugin ...` and `simple wrapper-gen ...`

### Direction A verification closure

- Added C++ `static_assert` layout emission in `src/compiler/90.tools/header_gen/cpp_header.spl`
- Added guarded `spl_library_init()` / `spl_library_shutdown()` definitions in `src/compiler/70.backend/backend/c_backend_translate.spl`
- Extended wrapper generator manifest output in `src/app/wrapper_gen/mod.spl`

## Verification

### Passing SSpec suites

- `test/unit/app/plugin/manifest_spec.spl`
- `test/unit/app/wrapper_gen/plugin_manifest_spec.spl`
- `test/unit/compiler/tools/header_gen_spec.spl`
- `test/unit/compiler/semantics/sffi_lint_spec.spl`
- `test/unit/compiler/types/layout_verification_spec.spl`
- `test/unit/compiler/common/export_attr_spec.spl`
- `test/system/sffi_bidirectional_interop_spec.spl`

### CLI smoke checks

- `src/compiler_rust/target/debug/simple plugin list` prints `no plugins registered`
- `src/compiler_rust/target/debug/simple wrapper-gen --help` prints the wrapper generator help text
- Both commands now execute without the earlier `std.io` import-resolution warning noise

### Rust compiler verification

- `cargo build -q -p simple-driver --bin simple` passed
- The full `cargo test -p simple-compiler plugin_manifest ...` path remained environment-sensitive because of the heavy compiler crate build/link step
- To close that gap, `src/compiler_rust/compiler/src/plugin_manifest.rs` was compiled and executed in an isolated Rust test harness against current source
- The embedded Rust unit tests and equivalent direct checks all passed:
  - `plugin_manifest::tests::parses_valid_manifest`
  - `plugin_manifest::tests::rejects_duplicate_symbols`
  - current-source valid-manifest parse check
  - current-source duplicate-symbol rejection check

## Residual

- The repo-local source and executable verification is complete
- The only remaining limitation is that the full crate-wide `cargo test -p simple-compiler plugin_manifest ...` path is still expensive in this workspace, but the manifest logic itself is now directly verified against current source
