# Simple MCP Release Guide

This repository now ships a releasable Claude Code plugin bundle for `simple-mcp`.

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

## Direct Release Asset Install

Download the tarball from the GitHub release and extract it into a Claude plugin directory:

```bash
curl -LO https://github.com/ormastes/simple/releases/download/v0.9.2/simple-mcp-claude-plugin-0.9.2.tar.gz
tar -xzf simple-mcp-claude-plugin-0.9.2.tar.gz
```

The bundle contains `.mcp.json` configured to run:

```bash
bin/simple_mcp_server
```

## Release Procedure

1. Build the plugin bundle:
   `sh tools/claude-plugin/package_release_plugins.shs --plugin simple-mcp --version <version> --output-dir build/release/plugins`
2. Upload the generated tarball to the matching GitHub release:
   `gh release upload v<version> build/release/plugins/simple-mcp-claude-plugin-<version>.tar.gz`
3. Keep JJ/Git in sync:
   `jj git fetch && jj rebase -d main@origin && jj bookmark set main -r @ && jj git push --bookmark main`
