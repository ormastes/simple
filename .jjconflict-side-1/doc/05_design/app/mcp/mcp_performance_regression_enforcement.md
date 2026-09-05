# MCP Performance Regression Enforcement Design

## Startup Path

The implementation uses one repo-owned executable, `scripts/mcp_performance_guard.py`, with subcommands for static audit, perf smoke, and verify. The build and CLI entrypoints call that executable directly through `python3`, so enforcement behavior stays in one place.

## Hot Path Inventory

The static audit inspects:
- `.mcp.json`
- `bin/t32_mcp_server`
- `bin/t32_lsp_mcp_server`
- `bin/obsidian_lsp_mcp_server`
- handler modules under `examples/**/src/mcp/` and `examples/**/src/lsp_mcp/`

The perf smoke suite measures:
- warm startup time and RSS for six user-facing wrappers
- a representative Obsidian `search_vault` request session against `test/fixtures/obsidian_perf_vault`

## Cache / Index Strategy

Wrapper rules require explicit compile-to-cache and execute-from-cache patterns. Handler rules forbid direct whole-tree primitives in request modules. The fixture vault is committed to the repo, and the smoke harness expands it into a temporary larger vault so request timings are stable enough to expose regressions.

## Invalidation Strategy

Invalidation is verified statically against the known mutation handler files. The guard fails if those modules stop referencing `invalidate_scan_vault_cache`.

## Performance Budgets

Budgets are stored in `scripts/mcp_performance_guard_config.json`:
- startup budgets in milliseconds and RSS MB
- request budgets in milliseconds

This keeps thresholds version-controlled and reviewable instead of hardcoded inside the build entrypoints.

## CLI Wiring

The implementation changes the CLI in three places:
- `simple lint --mcp-perf` runs the static audit
- `simple build check` runs static audit and perf smoke after the existing quality checks
- `simple verify` runs the combined verify mode instead of recursively invoking `./bin/simple verify`

## Failure Model

The guard is blocking. Any wrapper drift, forbidden hot-path primitive, missing invalidation marker, startup budget breach, request budget breach, or missing companion docs for MCP/tooling changes causes a non-zero exit code.
