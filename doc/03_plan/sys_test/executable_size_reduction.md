# Executable Size Reduction System Test Plan

Codex plan, 2026-04-23.

- Build/check affected Rust compiler native-project tests.
- Run `sh scripts/check-executable-size-budgets.shs --skip-missing` against available local artifacts.
- For compiler/runtime release readiness, run `sh scripts/check-core-runtime-smoke.shs <runtime>` and `SIMPLE_BINARY=<runtime> sh scripts/check-mcp-native-smoke.shs` when a fresh runtime is available.
- Confirm packaged MCP/LSP native-build commands include `--strip`.
