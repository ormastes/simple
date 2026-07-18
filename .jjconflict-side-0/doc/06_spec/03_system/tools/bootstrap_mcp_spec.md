# Bootstrap MCP Deployed Layout Specification

> Verify that bootstrap deployment leaves executable MCP/LSP release artifacts
> and executable `bin/` launchers. Protocol behavior belongs to the canonical
> command-line handshake spec and fresh native smoke checker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 6 | 6 | 0 | 0 |

## Scope

This manual mirrors
`test/03_system/tools/bootstrap_mcp_spec.spl`. It covers deployed file layout
only. It does not duplicate MCP framing, handshake, or feature-call behavior.

The executable protocol owners are:

- `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` for the
  Stage 2 cached MCP artifact.
- `scripts/check/check-mcp-native-smoke.shs` for the exact fresh Stage 5
  `simple_mcp_server` and `simple_lsp_mcp_server` pair.

## Acceptance

| Requirement | Assertion |
|-------------|-----------|
| MCP release artifact | `bin/release/<triple>/simple_mcp_server` exists and is executable |
| LSP release artifact | `bin/release/<triple>/simple_lsp_mcp_server` exists and is executable |
| MCP launcher | `bin/simple_mcp_server` exists and is executable |
| LSP launcher | `bin/simple_lsp_mcp_server` exists and is executable |

Missing artifacts fail the scenarios. There are no environment skips,
placeholder passes, source fallbacks, or masked process failures.

## Scenarios

### Bootstrap MCP — binary existence

#### simple_mcp_server binary exists at platform release path

Resolve the host platform triple, require the release artifact to exist, then
require `test -x` to return exit code `0`.

#### simple_lsp_mcp_server binary exists at platform release path

Resolve the host platform triple, require the release artifact to exist, then
require `test -x` to return exit code `0`.

### Bootstrap MCP — deployed launchers

#### bin/simple_mcp_server launcher exists

Require `bin/simple_mcp_server` to exist.

#### bin/simple_lsp_mcp_server launcher exists

Require `bin/simple_lsp_mcp_server` to exist.

#### bin/simple_mcp_server is executable

Require `test -x bin/simple_mcp_server` to return exit code `0`.

#### bin/simple_lsp_mcp_server is executable

Require `test -x bin/simple_lsp_mcp_server` to return exit code `0`.

## Protocol Evidence

Every bootstrap route that reaches the full server-producing Stage 5 deletes
and rebuilds both destinations with `SIMPLE_NO_STUB_FALLBACK=1`. Before deploy,
the native smoke sends `initialize`, `notifications/initialized`, and
`tools/list`, then requires successful `simple_status` and `lsp_symbols`
responses with exact correlated string IDs. Missing/stale binaries, timeouts,
malformed frames, JSON-RPC errors, and MCP `isError` results fail closed.

## Source

- Executable spec: `test/03_system/tools/bootstrap_mcp_spec.spl`
- Requirement: `doc/02_requirements/app/build/bootstrap.md`
- Handshake guide: `doc/07_guide/tooling/mcp_handshake_regression.md`

Manual synchronized on 2026-07-15. Regenerate with the pure-Simple SPipe
docgen after a fresh self-hosted CLI is available.
