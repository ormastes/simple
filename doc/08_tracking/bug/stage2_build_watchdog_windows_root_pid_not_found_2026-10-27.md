# stage2-build-watchdog.shs: "root pid N not found in process snapshot" on Windows

Status: fixed in the PR that adds this file (follow-up to PR #4918).

## Symptom
On Git-Bash/MSYS, both `-- CMD` and `--root-pid <Win32 pid>` modes could print
`VERDICT — ERROR could not monitor: root pid N not found in process snapshot`
on the first sample while the tree was alive. In `--` mode the exit path
`kill "$child"` signalled only the MSYS pid (not the Win32 tree), so the real
child was orphaned and kept writing to a log nobody was watching.

## Cause
- MSYS `$!` is not the Win32 PID; the mapping (`/proc/<pid>/winpid`) was read
  AFTER the Get-CimInstance snapshot, so an MSYS fork/exec PID swap between the
  two left the snapshot searched for a stale PID. Any miss on sample 0 was
  fatal (no retry).
- No fallback when `/proc/<pid>/winpid` was unreadable (`ps -W` WINPID column).
- Error paths used `kill` on the MSYS pid only; no EXIT trap, so the Win32 tree
  survived a watchdog error or Ctrl-C.
- Snapshot lines were not validated as numeric rows before the tree walk.

## Fix
winpid is re-mapped before every snapshot (with `ps -W` fallback); a missing
root while the MSYS child is alive is retried (re-map + re-snapshot, 4 tries)
instead of failing; every error path and the EXIT trap run `kill_child`
(`taskkill /F /T` of the Win32 tree); the child log is appended directly and
survives. Added `--min-commit-free-gb` (default 16; Win32 FreeVirtualMemory,
Linux MemAvailable) which, with `--kill-on-rss`, kills the tree like the RSS
cap does. Selftest gained real-child RSS-cap and commit-floor KILLED fixtures.

Reference: another agent's `capwatch.ps1` (64 GB tree working-set cap or <16 GB
free commit).
