# Executable Size Reduction Detail Design

Codex design, 2026-04-23.

## Runtime Symbol Retention

The linker reads global defined symbols from the selected runtime archive/object and global undefined symbols from generated objects, the main stub, and the generated init caller. It keeps only undefined symbols that the runtime actually defines, avoiding `-u` roots that would create new unresolved link failures.

Additional roots cover runtime lifecycle and indirect lookup paths: `__simple_runtime_init`, `__simple_runtime_shutdown`, `rt_set_args`, `rt_function_not_found`, string creation/access, and array creation/length.

## Release Size Check

The size script accepts explicit artifact paths or defaults to common local artifacts. It checks bytes with `wc -c`, classifies the artifact with `file`, applies basename-based budgets, and rejects unstripped release/package executables.

## Tests

Rust unit coverage builds tiny C objects and verifies that the runtime-retention set includes object undefineds and required roots while excluding unused runtime symbols.

## Loader Closure Detail

`simple-runtime-abi` reuses the existing runtime symbol-name list and adds a small registration surface:

- `RuntimeSymbolEntry`
- `register_static_runtime_symbols`
- `lookup_registered_static_runtime_symbol`

`simple-runtime` generates `RUNTIME_SYMBOL_ENTRIES` at build time from `RUNTIME_SYMBOL_NAMES`, filters that list to symbols actually defined in the default runtime build, and registers the resulting static slice during initialization. `simple-native-loader::StaticSymbolProvider` now delegates to the ABI registry instead of importing `simple-runtime`.

## Loader Dependency Audit

`scripts/check-loader-dependency-closure.shs` uses `cargo metadata`, `cargo tree`, and manifest parsing to report:

- direct dependencies for `simple-loader`, `simple-native-loader`, `simple-common`, and `simple-native-all`
- classification as normal, platform-gated, feature-gated, or test-only
- the normal transitive startup-path set for `simple-native-loader`

It fails when:

- `simple-native-loader` regains `simple-runtime` in its normal dependency tree
- a loader-crate direct dependency set diverges from the documented allowlist

## Native Binary Audit Detail

`scripts/check-native-binary-dependency-closure.shs` extends the feature from loader-only closure to binary-root closure.

It inspects the common local native outputs for:

- CLI binaries from debug/release/release-opt/bootstrap roots
- packaged CLI/MCP/LSP binaries under `bin/release/...`

For each available artifact it records:

- artifact path and build root
- `file` classification
- `readelf` `DT_NEEDED` shared libraries when available
- `ldd` loaded libraries when supported by the host

It also inspects the Rust build roots:

- `simple-driver`
- `simple-native-all`

For each root it reports:

- direct dependencies with bucket/mode classification
- normal startup-path transitive closure from `cargo tree`
- suspect groups such as runtime-service crates, interactive CLI crates, native-build overreach, and hosted-surface crates

## Follow-On Fix Targets

The audit is expected to keep surfacing two priority seams until they are refactored:

1. `simple-native-all -> simple-driver`
   This is the primary reason native-built MCP/LSP binaries inherit CLI-only dependencies.
2. broad default `simple-runtime` service crates
   This keeps package/network/TLS/compression functionality on the CLI startup path even for commands that do not need it.

The current implementation is intentionally diagnostic rather than pretending to solve those broader refactors in the same change.
