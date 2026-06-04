# Executable Size Reduction System Test Plan

Codex plan, 2026-04-23.

- Build/check affected Rust compiler native-project tests.
- Run `sh scripts/check/check-loader-dependency-closure.shs`.
- Run `sh scripts/check/check-native-binary-dependency-closure.shs --skip-missing`.
- Run `sh scripts/check/check-executable-size-budgets.shs --skip-missing` against available local artifacts.
- For compiler/runtime release readiness, run `sh scripts/check/check-core-runtime-smoke.shs <runtime>` and `SIMPLE_BINARY=<runtime> sh scripts/check/check-mcp-native-smoke.shs` when a fresh runtime is available.
- Confirm packaged MCP/LSP native-build commands include `--strip`.
