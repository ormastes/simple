# Simple MCP Release Guide

This repository ships a Claude Code plugin bundle for `simple-mcp` that is
intended to be used from a Simple repository checkout.

## What Was Added

- `tools/claude-plugin/simple-mcp/`:
  - `.claude-plugin/plugin.json`
  - `.mcp.json`
  - `README.md`
- `tools/claude-plugin/marketplace/plugins/simple-mcp/`:
  - `.claude-plugin/plugin.json`
  - `.mcp.json`
  - `README.md`
- `tools/claude-plugin/marketplace/.claude-plugin/marketplace.json`:
  - registers `simple-mcp@simple-local`
- `tools/claude-plugin/package_release_plugins.shs`:
  - packages `simple-mcp-claude-plugin-<version>.tar.gz`

## Where It Is Released

The plugin bundle is released on the main GitHub release page for this repository:

- Repository: `https://github.com/ormastes/simple`
- Release page: `https://github.com/ormastes/simple/releases`
- Current runtime release used for upload in this session: `v0.9.2`

Uploaded asset name:

- `simple-mcp-claude-plugin-0.9.2.tar.gz`

## Local Marketplace Install

From a checkout of this repository:

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-mcp@simple-local
```

## Release Asset Semantics

The `simple-mcp-claude-plugin-<version>.tar.gz` asset is a plugin metadata
bundle for repo-based installation. It is not a standalone portable runtime
bundle.

The extracted bundle still expects to run from a Simple repository root that
contains:

- `bin/simple_mcp_server`
- `bin/release/simple` or a platform release runtime
- `src/app/mcp/main.spl`

If you want to use `simple-mcp` without the Claude plugin bundle, register the
MCP server directly from a repository checkout:

```bash
claude mcp add simple-mcp -- \
  /absolute/path/to/simple/bin/release/simple \
  /absolute/path/to/simple/src/app/mcp/main.spl
```

## Release Procedure

1. Build the plugin bundle:
   `sh tools/claude-plugin/package_release_plugins.shs --plugin simple-mcp --version <version> --output-dir build/release/plugins`
2. Upload the generated tarball to the matching GitHub release:
   `gh release upload v<version> build/release/plugins/simple-mcp-claude-plugin-<version>.tar.gz`
3. Keep JJ/Git in sync:
   `jj git fetch && jj rebase -d main@origin && jj bookmark set main -r @ && jj git push --bookmark main`
