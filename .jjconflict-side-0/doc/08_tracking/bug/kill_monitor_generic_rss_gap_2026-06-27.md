# Kill Monitor Generic RSS Gap - 2026-06-27

## Status

Fixed in `scripts/resource/kill_simple_monitor.shs`.

## Problem

The background kill monitor only enforced RSS and CPU kill rules for
`bin/simple run` and `bin/simple test` processes. A rogue non-Simple process
owned by the same user, such as a leaking `python3` helper, could grow until an
external OOM guard intervened. That made post-crash diagnosis weak because the
offending command line disappeared with the process.

## Fix

- Added warning logs for any owned non-protected process above
  `KILL_SIMPLE_WARN_MB` so the command line is recoverable.
- Added `KILL_ANY_MEM_MB` as a high generic RSS cap for non-protected owned
  processes.
- Kept MCP, LSP, tmux, Claude, Codex, node, and npm process protections.
- Updated `scripts/resource/kill_simple_monitor_test.shs` to cover uid-aware
  rows, Simple RSS, Simple CPU, generic RSS, protected, young, healthy, and
  root-owned cases.

## Verification

`sh scripts/resource/kill_simple_monitor_test.shs`

Expected result:

`PASS kill_simple_monitor: killed [1001 1002 3004] (simple mem, simple cpu, generic mem), spared healthy/protected/young/root-owned`
