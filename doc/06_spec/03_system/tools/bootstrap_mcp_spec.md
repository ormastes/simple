# Bootstrap MCP Deployment Sanity Specification

> Verify that bootstrap deployment leaves admitted MCP/LSP release artifacts,
> matching integrity sidecars, and working `bin/` launchers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 9 | 9 | 0 | 0 |

## Scope

This manual mirrors
`test/03_system/tools/bootstrap_mcp_spec.spl`. It covers deployed layout,
artifact integrity, the MCP native probe, and a bounded LSP symbols admission
through the launcher. It does not duplicate the broader LSP feature suite.

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
| Integrity admission | Both release artifacts have matching `.sha256` sidecars |
| MCP launcher | `bin/simple_mcp_server` exists and is executable |
| LSP launcher | `bin/simple_lsp_mcp_server` exists and is executable |
| MCP startup | `bin/simple_mcp_server --probe` reports `probe ok` |
| LSP wrapper admission | From a non-repository CWD, hash-admitted launcher restores the canonical repository root and returns correlated `initialize`, `tools/list`, and `lsp_symbols` results |

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

#### native MCP binaries have matching integrity sidecars

Require each sibling `.sha256` file to exist and equal the executable's
computed SHA-256 digest.

### Bootstrap MCP — deployed launchers

#### bin/simple_mcp_server launcher exists

Require `bin/simple_mcp_server` to exist.

#### bin/simple_lsp_mcp_server launcher exists

Require `bin/simple_lsp_mcp_server` to exist.

#### bin/simple_mcp_server is executable

Require `test -x bin/simple_mcp_server` to return exit code `0`.

#### bin/simple_lsp_mcp_server is executable

Require `test -x bin/simple_lsp_mcp_server` to return exit code `0`.

#### deployed MCP launcher passes its native startup probe

Run the deployed MCP wrapper with `--probe`, require exit code `0`, and require
the native server's `probe ok` marker.

#### deployed LSP MCP launcher passes correlated symbols admission

Read the deployed wrapper contract to require `native_hash_is_valid`, its
canonical `cd "${repo_root}"`, and the bounded native probe. Then invoke the
launcher from a temporary non-repository CWD with a 10-second `timeout`,
`gtimeout`, or Perl alarm bound. Send correlated `initialize`, `tools/list`,
and `tools/call(lsp_symbols)` requests. Require exit code `0`, each matching
result ID, `lsp_symbols` advertised by the list, and a usable symbol object whose
escaped `name` field is exactly `log_options_help`. Reject JSON-RPC `error`, MCP
`isError`, text-only mentions, and child-command-failure output.

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

Manual synchronized on 2026-07-23. Regenerate with the pure-Simple SPipe
docgen after the fresh self-hosted MCP artifacts are deployed.
