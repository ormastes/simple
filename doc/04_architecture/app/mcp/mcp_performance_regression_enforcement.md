# MCP Performance Regression Enforcement

## Startup Path

Production MCP and LSP launchers are treated as wrapper-bound interfaces. The enforcement system checks both `.mcp.json` and launcher scripts so user-facing servers must launch cached compiled artifacts instead of raw `.spl` entrypoints.

## Hot Path Inventory

The guarded hot paths are:
- MCP and LSP handler modules under `examples/**/src/mcp/` and `examples/**/src/lsp_mcp/`
- user-facing wrapper scripts in `bin/`
- `build check`, `lint --mcp-perf`, and `verify`

These are the places where startup cost, repeated scans, and synchronous subprocesses become user-visible regressions.

## Cache / Index Strategy

The prevention layer does not build new caches itself. It verifies that production wrappers compile into cached `.smf` artifacts and that request handlers avoid direct whole-tree primitives such as `rt_dir_walk` or `scan_vault_with_excludes`.

## Invalidation Strategy

Mutation handlers that update Obsidian vault content must reference `invalidate_scan_vault_cache`. The guard treats the write, metadata, search-extension, and periodic handlers as required invalidation points.

## Performance Budgets

The repo-owned budget source is `scripts/mcp_performance_guard_config.json`.

Blocking thresholds:
- warm startup for `simple-mcp` and `simple-lsp-mcp`
- warm startup for `t32-*` and `obsidian-*` wrappers
- representative `obsidian-search/search_vault` request latency on the committed fixture vault

## Enforcement Surfaces

The guard runs in three modes:
- `static-audit`: wrapper config, wrapper content, hot-path pattern, and invalidation checks
- `perf-smoke`: warm startup and representative request latency checks
- `verify`: static audit, perf smoke, and doc traceability as a blocking gate

`build check` runs the static audit and perf smoke. `verify` runs the full combined gate.
