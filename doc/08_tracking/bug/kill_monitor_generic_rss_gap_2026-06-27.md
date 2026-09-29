# Kill Monitor Generic RSS Gap - 2026-06-27

## Closed 2026-09-13 — generic RSS cap is present in the monitor script
- **measured**: `grep -c KILL_ANY_MEM_MB scripts/resource/kill_simple_monitor.shs` = 5 — the generic non-protected-process cap this entry adds is in the tree.
- **inferred**: the monitor is a Linux/procfs RSS watchdog and was not executed on this Windows host; the fix is verified present, not verified running.
- **inferred**: the entry's own status was already "Fixed"; this closure records that the change survived and was not reverted.

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
