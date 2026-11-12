# `mcp-t32` CLI subcommand is not registered in the CLI command registry

**Status:** OPEN 2026-11-12 — found by the p1-t32 lane while making `test/03_system/feature/app/t32_tools/**` run on the phase-1 seed.
**Severity:** Tooling gap (P3). The TRACE32 MCP server is fully usable through the tracked launcher `bin/t32_mcp_server.cmd` (and the install.shs-generated POSIX `bin/t32_mcp_server`), so nothing is blocked; only the documented `bin/simple mcp-t32` entry point is missing.
**Affected files:** `src/app/cli/command_registry.spl` (registry rows), `src/app/cli/help_surface_generated_data.spl` (identity receipt), `src/app/cli/_CliMain/main_and_help.spl` (dispatch arm).
**Spec files:** `test/03_system/feature/app/t32_tools/t32_mcp_bugfix_spec.spl` "Bug 3a" (rescoped to the current contract), `t32_mcp_wrapper_spec.spl` (launcher end-to-end).

## Symptom

`get_command_table()` has a `t32` row but no `mcp-t32` row, so
`bin/simple mcp-t32` is "unknown command". The old Bug 3a spec items asserted
the row existed; the second item was vacuous (loop with no match passed).

## Why it was not fixed in this lane

Adding `_cmd("mcp-t32", ..., "examples/10_tooling/trace32_tools/t32_mcp/main.spl")`
makes `test/01_unit/app/cli/help_surface_inventory_spec.spl` and
`help_surface_production_parity_spec.spl` fail: the generated CLI surface
receipt (`CLI_SURFACE_HELP_SOURCE_SHA256_V1` etc.) pins the registry source
hash and "Core commands unavailable: generated CLI surface is stale" is
emitted until the receipt is regenerated and a dispatch needle exists in
`main_and_help.spl`. That is a CLI-owner change (receipt regeneration +
dispatch arm), out of scope for the t32 tooling lane; reverted here.

## Unblock condition

CLI owner adds the registry row, the dispatch arm, regenerates the receipt,
and restores the two original Bug 3a assertions (presence + `app_path`
contains `t32_mcp/main.spl`, asserting the match count rather than looping
vacuously).
