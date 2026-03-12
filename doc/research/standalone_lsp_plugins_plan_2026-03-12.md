# Standalone LSP Plugins Plan — Simple and T32 Tools

**Date:** 2026-03-12
**Status:** Planned

## Goal

Produce two standalone Claude Code LSP plugin packages:

1. `simple-lsp` for `.spl` / `.shs`
2. `cmm-lsp` for `.cmm`

Standalone means:
- the released plugin package does not depend on repo-relative source paths
- `.lsp.json` launches shipped executables only
- the package can be installed without a source checkout

## Current State

### Simple

What exists:
- Simple LSP server source at `src/lib/nogc_sync_mut/lsp/`
- build support for `simple_lsp`
- CLI/script entrypoint via `src/lib/nogc_sync_mut/lsp/main.spl`

What does not exist in this repo:
- checked-in `tools/claude-plugin/simple-lsp/`
- standalone release packaging for a Simple Claude plugin

Important mismatch:
- `bin/release/simple lsp --help` is not currently a reliable packaged entrypoint
- `bin/release/simple src/lib/nogc_sync_mut/lsp/main.spl --help` does work

### T32 / CMM

What exists:
- checked-in dev plugin bundle at `examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp/`
- standalone `cmm-lsp` executable built by T32 workflows
- release packaging for `cmm-lsp-claude-plugin-${VERSION}.tar.gz`

Current problem:
- the packaged `.lsp.json` still points at repo-relative source paths:
  `bin/release/simple examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp`
- that makes the released tarball non-standalone

## Target Packaging Model

Use two bundle classes:

### 1. Dev bundle in repo

Purpose:
- contributor install from checkout
- can point at workspace-relative paths

Examples:
- `tools/claude-plugin/simple-lsp/`
- `examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp/`

### 2. Release bundle

Purpose:
- standalone install from release assets
- must point only at shipped binaries

Examples:
- `simple-lsp-claude-plugin-${VERSION}.tar.gz`
- `cmm-lsp-claude-plugin-${VERSION}.tar.gz`

## Required Design Rule

Release-time `.lsp.json` must use executable names, not source paths.

Required pattern:

```json
{
  "languages": [
    {
      "languageId": "...",
      "fileExtensions": ["..."],
      "command": ["simple-lsp"]
    }
  ]
}
```

or:

```json
{
  "languages": [
    {
      "languageId": "cmm",
      "fileExtensions": [".cmm"],
      "command": ["cmm-lsp"]
    }
  ]
}
```

This keeps the plugin package independent from the repo layout.

## Plan

### Phase 1. Stabilize binary entrypoints

#### Simple

Make one binary contract official:
- `simple-lsp`

Requirements:
- works with `--help`
- works with `--version`
- runs LSP over stdio directly
- does not require `simple <script-path>`

Implementation options:
- fix `simple lsp` dispatch so it is valid for plugin use
- or ship a dedicated `simple-lsp` binary and treat that as canonical

Recommended:
- ship a dedicated `simple-lsp` executable
- keep `simple lsp` as convenience only

Reason:
- plugin packages should not depend on CLI subcommand routing quirks

#### CMM

Keep the canonical binary:
- `cmm-lsp`

No source-path-based command should appear in release plugin assets.

### Phase 2. Check in dev plugin bundles

#### Simple

Create:

```text
tools/claude-plugin/simple-lsp/
  .claude-plugin/plugin.json
  .lsp.json
  README.md
```

Dev bundle command:
- may temporarily use a verified repo-local command

Preferred if available:
- `["bin/release/simple-lsp"]`

Fallback only if necessary:
- `["bin/release/simple", "src/lib/nogc_sync_mut/lsp/main.spl"]`

#### CMM

Keep:
- `examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp/`

But document clearly that this is the dev/install-from-checkout bundle.

### Phase 3. Generate release plugin bundles

Do not release the checked-in dev `.lsp.json` unchanged.

Instead, generate release-time plugin bundles whose `.lsp.json` uses:
- `simple-lsp`
- `cmm-lsp`

Suggested release asset contents:

#### Simple

```text
simple-lsp
simple-lsp-claude-plugin-${VERSION}.tar.gz
```

#### T32 / CMM

```text
cmm-lsp
cmm-lsp-claude-plugin-${VERSION}.tar.gz
```

Suggested release tarball structure:

```text
simple-lsp/
  .claude-plugin/plugin.json
  .lsp.json
  README.md
```

and:

```text
cmm-lsp/
  .claude-plugin/plugin.json
  .lsp.json
  README.md
```

### Phase 4. Validate in CI

For both projects, CI should verify:
- binary exists
- binary `--help` works
- binary `--version` works
- plugin bundle files exist
- release `.lsp.json` contains executable command only
- release `.lsp.json` contains no repo-relative source paths

Required negative checks:
- reject `.lsp.json` containing `examples/`
- reject `.lsp.json` containing `src/`

### Phase 5. Align docs

Docs should distinguish:
- dev bundle in repo
- standalone release plugin package
- standalone executable binary

Never describe the plugin package as a binary.

## Concrete Deliverables

### Simple deliverables

1. `tools/claude-plugin/simple-lsp/`
2. stable `simple-lsp` executable
3. release asset `simple-lsp-claude-plugin-${VERSION}.tar.gz`
4. docs updated to point at actual checked-in bundle

### T32/CMM deliverables

1. keep `examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp/`
2. patch release packaging so release `.lsp.json` launches `cmm-lsp`
3. keep release asset `cmm-lsp-claude-plugin-${VERSION}.tar.gz`
4. docs clearly separate dev bundle vs release bundle

## Recommended Execution Order

1. Fix Simple binary entrypoint and ship `simple-lsp`
2. Check in `tools/claude-plugin/simple-lsp/`
3. Change T32 release plugin generation to use `cmm-lsp`
4. Add generated release plugin for Simple
5. Add CI assertions preventing repo-relative commands in release plugin bundles

## Bottom Line

If the Simple plugin exists somewhere outside this repo, that is not enough for
repo correctness.

For this repo to be internally consistent:
- Simple needs a checked-in dev plugin bundle plus a standalone released plugin
- T32/CMM needs release-time plugin generation that targets `cmm-lsp`, not
  repo-relative script paths
