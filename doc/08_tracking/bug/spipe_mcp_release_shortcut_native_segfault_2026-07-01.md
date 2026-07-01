# Bug: SPipe MCP Release Shortcut Native Binary Segfaults

Date: 2026-07-01
Status: open
Severity: P1 for release shortcut deployment

## Summary

`simple spipe-mcp ...` is wired in source, but the checked-in release binary is
stale and a freshly native-built CLI binary segfaults when dispatching app
subcommands. Do not deploy the rebuilt binary until the native app-subcommand
crash is fixed.

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

## Next Step

Debug native app-subcommand dispatch from `src/app/cli/main.spl` through
`src/app/io/_CliCommands/run_commands.spl`. After that is fixed, rebuild the
release binary and re-run:

```sh
bin/release/simple spipe-mcp parsers
bin/release/simple spipe-mcp minimality-check --task='add date picker'
```
