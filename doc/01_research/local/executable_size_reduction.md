# Executable Size Reduction - Local Research

Codex findings, 2026-04-23.

## Baseline Snapshot

Measured from the current workspace before implementation:

| Artifact | Bytes | Notes |
| --- | ---: | --- |
| `src/compiler_rust/target/bootstrap/simple` | 50,523,368 | ELF, reported with debug info and not stripped in the existing local build |
| `src/compiler_rust/target/bootstrap/libsimple_runtime.a` | 68,954,304 | static archive |
| `src/compiler_rust/target/bootstrap/libsimple_native_all.a` | 65,161,518 | static archive |
| `bin/simple_mcp_server` | 5,042,368 | symlink target under `bin/release/x86_64-unknown-linux-gnu/` |
| `bin/simple_lsp_mcp_server` | 4,561,752 | symlink target under `bin/release/x86_64-unknown-linux-gnu/` |

## Existing Mechanisms

`src/compiler_rust/Cargo.toml` already defines `release-opt` with stripping, fat LTO, one codegen unit, and panic abort. The `bootstrap` profile inherits it, switches to size optimization, thin LTO, and panic unwind for native-build compatibility.

Native generated object support already uses `-ffunction-sections` and `-fdata-sections` for generated helper objects and passes `--gc-sections` on ELF links. The size problem was that `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` still force-loaded `libsimple_native_all.a` with `--whole-archive` on ELF, which defeats archive-member garbage collection.

Release packaging in `.github/workflows/release.yml` builds native MCP and LSP package binaries from the bootstrap runtime. Before this change, those native-build invocations did not pass `--strip`, and no release-size budget script checked packaged outputs.

## Dependency Audit

`reqwest` is not present in active workspace manifests outside vendored/dev dependency references. Current active size candidates remain `ureq`, `socket2`, TLS, archive/compression crates, and terminal/UI dependencies, but no dependency split was made in this change because the measured linker and guardrail bugs are narrower and lower risk.

## Implemented Fix Surface

- ELF native-build runtime linking now retains only symbols derived from generated object undefined references plus explicit runtime lifecycle/string/dispatch roots. `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` preserves the old behavior for diagnostics.
- Release package MCP and LSP native-build steps pass `--strip`.
- `scripts/check-executable-size-budgets.shs` checks budgets for CLI, MCP, LSP, native executables, and `libsimple_runtime.a`.

## Loader Dependency Closure Follow-On

Codex follow-on findings, 2026-04-28.

### Dependency Audit

- `simple-native-loader` previously had a normal dependency on `simple-runtime` only to materialize the static symbol provider table. That pulled the full runtime crate graph onto the loader startup path.
- The runtime ABI surface already existed in `simple-common`, but it was bundled with unrelated common utilities and their heavier transitive set (`ahash`, `serde`, `memmap2`, `serde_json`, `tracing`, `thiserror`).
- `simple-loader` had stale direct dependencies on `sha1`, `xxhash-rust`, `memmap2`, and `bincode` even though no source file in `src/compiler_rust/loader/src/` imported them directly.
- `simple-native-all` and `spl_hosted_runtime` already keep the stub-only default posture. No feature broadening was needed for this pass.

### Measured Loader Artifacts

Measured locally from the current workspace after the loader-closure implementation:

| Artifact | Bytes | Notes |
| --- | ---: | --- |
| `src/compiler_rust/target/debug/deps/libsimple_native_loader-1819d557257af4e6.rlib` | 2,422,926 | debug rlib |
| `src/compiler_rust/target/debug/deps/libsimple_native_loader-b1ce1de22c7739d6.rlib` | 2,867,840 | test-profile rlib |
| `src/compiler_rust/target/bootstrap/libsimple_runtime.a` | 68,954,304 | bootstrap static archive |
| `src/compiler_rust/target/bootstrap/libsimple_native_all.a` | 66,719,956 | bootstrap static archive |
| `bin/simple_mcp_server` | 23,367,440 | package-linked server |
| `bin/simple_lsp_mcp_server` | 22,981,120 | package-linked server |

### Implemented Closure

- Added `simple-runtime-abi` as the dedicated owner of `AbiVersion`, `RuntimeSymbolProvider`, `RUNTIME_SYMBOL_NAMES`, and static symbol registration.
- `simple-native-loader` now depends on `simple-runtime-abi` instead of `simple-runtime`.
- `simple-runtime` now generates and registers its static symbol table through the ABI crate during build/runtime initialization.
- `scripts/check-loader-dependency-closure.shs` enforces the direct-dependency allowlists and fails if `simple-native-loader` regains a normal dependency on `simple-runtime`.

## Native Binary Dependency Architecture Follow-On

Codex per-binary audit findings, 2026-04-28.

### OS-Loaded Module Surface

Measured on the current Linux workspace:

| Executable | Dynamic libs observed | Main takeaway |
| --- | --- | --- |
| `bin/release/x86_64-unknown-linux-gnu/simple` | `libm`, `libunwind`, `libstdc++`, `libgcc_s`, `libc` | The ELF `DT_NEEDED` set is already narrow. |
| `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` | `libm`, `libunwind`, `libstdc++`, `libgcc_s`, `libc` | Package MCP binary is not over-linking extra shared libraries. |
| `bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server` | `libm`, `libunwind`, `libstdc++`, `libgcc_s`, `libc` | LSP package binary has the same narrow dynamic surface. |
| `src/compiler_rust/target/bootstrap/simple` | `libgcc_s`, `libm`, `libc` | Bootstrap CLI is dynamically small too. |

The primary size/startup problem has shifted from dynamic loader over-linking to **static crate/module closure** retained through coarse Rust binary roots and `native-build` archive roots.

### Per-Binary Rust Root Findings

- `simple-driver` is the root crate for the CLI variants and currently keeps broad subsystems on the default startup path:
  - runtime service/network/package crates through `simple-runtime`: `socket2`, `ureq`, `rustls`, `webpki-roots`, `tar`, `flate2`, `xz2`
  - interactive/auth/watcher crates through direct driver deps: `rustyline`, `notify`, `sysinfo`, `rpassword`, `argon2`, `hostname`
- `simple-native-all` is the effective root for `native-build` package outputs such as `simple_mcp_server` and `simple_lsp_mcp_server`.
- `simple-native-all` currently depends directly on `simple-driver`, which means native-built servers inherit CLI-only subsystems they do not need on their startup path.
- `spl_hosted_runtime` is still part of the `simple-native-all` root. Its default features remain stub-only, so this is lower priority than the `simple-native-all -> simple-driver` edge, but it is still a real architecture dependency.

### Highest-Value Architecture Issues

1. `simple-native-all -> simple-driver`
   Native-built MCP/LSP outputs currently inherit broad CLI subsystems because the archive root includes driver hooks and test-runner/file-execution helpers by depending on all of `simple-driver`.
2. `simple-driver -> simple-runtime` with broad default runtime services
   Runtime networking/package/compression crates are present even on plain CLI startup paths where most commands do not need them.
3. Coarse single-binary CLI composition
   REPL, watcher, auth/qualified-ignore, and other command-family dependencies stay resident in the default CLI root rather than narrower helper crates or feature capsules.

### Implemented Audit Surface

- Added `scripts/check-native-binary-dependency-closure.shs` to report:
  - common native executable artifacts found in the local workspace
  - `readelf` / `ldd` loaded-module surfaces where applicable
  - direct dependency lists for `simple-driver` and `simple-native-all`
  - startup-path crate closures and suspect architecture edges
- The script is intentionally report-first: it fails on missing required artifacts or root-dependency drift, and reports architecture suspects without pretending they are fixed yet.
