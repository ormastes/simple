# Executable Size Reduction Architecture

Codex design, 2026-04-23.

The change stays inside existing build boundaries.

## Native Build Link Layer

`NativeProjectBuilder::link_objects` remains the native link orchestrator. On ELF platforms, `libsimple_native_all.a` now links as a normal archive after adding `-Wl,-u,<symbol>` roots. The root set is computed from generated object undefined symbols intersected with runtime-defined symbols, plus a small explicit list for runtime lifecycle, argument, dispatch, string, and array entrypoints.

`SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` selects the old force-load behavior for diagnostics.

## Release Package Layer

`.github/workflows/release.yml` continues to build native MCP/LSP binaries with the bootstrap runtime, but passes `--strip` and then calls `scripts/check-executable-size-budgets.shs` on package outputs.

## Guardrail Layer

`scripts/check-executable-size-budgets.shs` owns byte budgets and release-strip checks. Budgets are configurable through environment variables so release maintainers can adjust thresholds without editing workflow logic.

## Loader ABI Layer

The runtime symbol ABI now lives in `simple-runtime-abi`, not `simple-common` or `simple-runtime`. `simple-native-loader` consumes that crate for `AbiVersion`, `RuntimeSymbolProvider`, `RUNTIME_SYMBOL_NAMES`, and registered static symbol lookup. `simple-runtime` remains the implementation owner of the actual symbol functions and publishes its static registration table through the ABI crate.

This keeps the primary architecture seam narrow:

- `simple-native-loader -> simple-runtime-abi`
- `simple-runtime -> simple-runtime-abi`
- no normal `simple-native-loader -> simple-runtime` edge

## Loader Dependency Guardrails

`scripts/check-loader-dependency-closure.shs` is the regression guard for the loader startup path. It checks direct-dependency allowlists for `simple-loader`, `simple-native-loader`, `simple-common`, and `simple-native-all`, then walks the `simple-native-loader` normal dependency tree and fails if `simple-runtime` reappears there.

## Native Binary Root Layer

The deeper architecture issue is now at the binary-root level rather than the ELF shared-library level.

- CLI binaries (`simple` debug/release/bootstrap/package variants) are rooted in `simple-driver`.
- Native-built MCP/LSP package binaries are rooted in `simple-native-all`, not a dedicated server crate.
- `simple-native-all` currently depends on `simple-driver`, so server outputs inherit CLI-only startup-path crates even when they only need runtime/compiler/native-build hooks.

Target dependency shape for the next refactor phase:

- `simple-driver` remains the broad CLI root.
- native-built server outputs must stop inheriting all of `simple-driver`.
- the native-build archive root should consume only:
  - runtime/compiler contracts needed for compiled entry closures
  - a small hook/provider crate for file execution or test execution if those hooks remain required
  - hosted-runtime stubs only when the selected entry/runtime bundle actually needs them

This is the next architecture seam after the loader ABI split:

- current: `simple-native-all -> simple-driver`
- target: `simple-native-all -> narrow native-build hook/provider crate`

## Runtime Service Layer

`simple-runtime` currently keeps network/package/service crates (`socket2`, `ureq`, `rustls`, `tar`, `flate2`, `xz2`, related TLS roots) on the default CLI startup path because the runtime crate owns both core execution facilities and optional service-style helpers.

The target architecture is to separate:

- runtime core execution path
- optional runtime service capsules such as network/package/compression support

The new per-binary audit script documents these edges so the next refactor can remove them with evidence rather than guessing.
