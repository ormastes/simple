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
