<!-- codex-research -->
# Simple MCP / LSP MCP Breakage — 2026-04-19

## Summary

Both `@simple-lang/mcp-server` and `@simple-lang/lsp-mcp-server` are currently broken for end users after `npm install`, even though the repo-local native builds still work.

The failure is in the published distribution path, not in the current source tree.

## Reproduction

Isolated install flow:

1. `npm pack` from `tools/mcp-registry` and `tools/lsp-mcp-registry`
2. `npm install` both tarballs into a fresh temp project
3. Send real MCP `initialize` and `tools/list` requests over stdio with `Content-Length` framing

Observed result for both commands:

- `simple-mcp-server`
- `simple-lsp-mcp-server`

Both exited with stderr:

`error: parse error: Unexpected token: expected expression, found Allow`

## What Still Works

Fresh native builds from the repo answered correctly:

- `src/app/mcp/main.spl`
- `src/app/simple_lsp_mcp/main.spl`

Verified behavior:

- `initialize` returned `protocolVersion: 2025-06-18`
- `tools/list` returned valid tool arrays for both servers

## Root Cause

The npm packages declare:

- package version: `0.9.6`
- `runtimeVersion`: `0.9.5`

Inside the installed bootstrap bundle for `simple-bootstrap-0.9.5-linux-x86_64`:

- the fallback runtime binary is `src/compiler_rust/bin/release/simple`
- that binary reports `Simple Language v0.8.1`
- the bundled MCP entry source starts with `@allow(unnamed_duplicate_typed_args)`

That means the shipped bootstrap bundle contains a runtime that is older than the source it is asked to parse. The older runtime chokes on `@allow(...)`, so startup fails before either server reaches protocol initialization.

This is why both MCP packages fail the same way.

## Why It Keeps Breaking

The release path has multiple independent versioned artifacts with no end-to-end compatibility check:

- npm package version
- `runtimeVersion` inside `package.json`
- GitHub bootstrap asset contents
- actual runtime binary version inside the bootstrap asset
- source tree bundled inside the bootstrap asset

Current deployment checks version strings and file presence, but not whether a real installed package can answer MCP requests.

## Immediate Prevention Added

New guard:

- `scripts/check-mcp-package-smoke.shs`

What it does:

1. Packs both npm tarballs locally
2. Installs them into a fresh temp project
3. Performs real `initialize` and `tools/list` probes against:
   - `simple-mcp-server`
   - `simple-lsp-mcp-server`
4. Fails with debug output showing bundled runtime version and entry file header

Publish path change:

- `scripts/deploy-marketplaces.shs` now runs the smoke test before `npm publish`

## Prevention Plan

### Phase 1: Release Gate

Keep the new smoke test mandatory for publish.

Success criteria:

- no npm publish without a passing isolated-install handshake test

### Phase 2: Bootstrap Consistency Check

Add a release-time validator for bootstrap assets that checks:

- bootstrap asset version matches expected release version
- bundled runtime `--version` matches the asset version
- bundled entrypoints parse under the bundled runtime

This should run before release assets are uploaded.

### Phase 3: Remove Runtime/Source Drift

Prefer shipping native `simple_mcp_server` and `simple_lsp_mcp_server` inside the bootstrap package and using those first in installed packages.

Reason:

- it removes the fallback path where one runtime parses a separately bundled source tree

### Phase 4: CI Coverage

Add CI jobs for:

- `npm pack` + isolated install + handshake
- bootstrap asset internal version check
- registry package verification for both MCP and LSP variants

### Phase 5: Release Policy

Do not publish npm package `X.Y.Z` unless a matching GitHub release asset set for `X.Y.Z` already exists, or unless the package intentionally embeds all required native binaries and does not depend on older bootstrap assets.

## Recommended Follow-Up

1. Build and publish a consistent bootstrap/runtime release.
2. Reinstall the npm packages in a clean temp project.
3. Re-run the smoke test.
4. Only then publish to npm and MCP Registry.
