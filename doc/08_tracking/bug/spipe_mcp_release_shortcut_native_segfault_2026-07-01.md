# Bug: SPipe MCP Release Shortcut Native Binary Segfaults

Date: 2026-07-01
Status: fixed
Severity: P1 for release shortcut deployment

## Summary

`simple spipe-mcp ...` is wired in source. A freshly native-built monolithic CLI
still segfaults when it imports and dispatches several app subcommands
in-process, but SPipe MCP has a working native entrypoint. The release shortcut
now delegates to an explicit/package SPipe MCP binary instead of importing the
app into the CLI binary.

## Evidence

Stale deployed binary:

```sh
bin/release/simple spipe-mcp parsers
# exit 1, falls through to old top-level help
```

Fresh native build:

```sh
mkdir -p build/spipe_mcp_shortcut
bin/release/simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/cli/main.spl --strip \
  -o build/spipe_mcp_shortcut/simple
# exit 0, produces build/spipe_mcp_shortcut/simple
```

Fresh binary behavior:

```sh
build/spipe_mcp_shortcut/simple --help
# exit 0

build/spipe_mcp_shortcut/simple spipe-mcp parsers
# exit 139, segmentation fault

build/spipe_mcp_shortcut/simple spipe-docgen --help
# exit 139, segmentation fault
```

This is broader than SPipe MCP because another app subcommand also crashes.
The source-mode SPipe MCP oracle still passes through:

```sh
bin/release/simple run scripts/smoke/spipe_mcp_protocol_smoke.spl
# STATUS: PASS spipe_mcp_protocol_smoke
```

The standalone SPipe MCP native entrypoint also passes:

```sh
mkdir -p build/spipe_mcp_direct
bin/release/simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/spipe_mcp/main.spl \
  -o build/spipe_mcp_direct/spipe_mcp
# exit 0, produces build/spipe_mcp_direct/spipe_mcp

build/spipe_mcp_direct/spipe_mcp parsers
# exit 0, prints parser names

build/spipe_mcp_direct/spipe_mcp help
# exit 0, prints SPipe MCP CLI help
```

That narrows the bug to top-level native CLI app-subcommand dispatch or native
codegen for the `src/app/cli/main.spl` import path, not the SPipe MCP parser
library or `src/app/spipe_mcp/main.spl` entrypoint.

Fixed shortcut behavior:

```sh
bin/release/simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/cli/main.spl \
  -o build/spipe_mcp_shortcut_fix/simple

bin/release/simple native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/spipe_mcp/main.spl \
  -o build/spipe_mcp_shortcut_fix/spipe_mcp

SIMPLE_SPIPE_MCP_BINARY=build/spipe_mcp_shortcut_fix/spipe_mcp \
  build/spipe_mcp_shortcut_fix/simple spipe-mcp parsers
# exit 0, prints parser names

SIMPLE_SPIPE_MCP_BINARY=build/spipe_mcp_shortcut_fix/spipe_mcp \
  build/spipe_mcp_shortcut_fix/simple spipe-mcp minimality-check --task='add date picker'
# exit 0, prints native-date minimality guidance
```

The package artifact lookup also works when the native SPipe MCP binary is
staged at `build/bootstrap/mcp-package/spipe_mcp`:

```sh
build/spipe_mcp_shortcut_fix/simple spipe-mcp parsers
# exit 0, prints parser names
```

## Remaining Native CLI Bug

The broader monolithic CLI native app-subcommand crash still exists outside the
SPipe MCP shortcut and should be tracked separately before converting other
app subcommands back to in-process native imports.
