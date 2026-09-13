# SimpleOS streaming exec has no registered process identity
**Status:** OPEN (unverified 2026-09-12)

The x86_64 raw-ELF streaming handoff runs synchronously and returns the program exit code, but it does not create a scheduler-owned task/process record. A PID must not be allocated solely for logging or receipts because no process with that identity exists.

REQ-001/REQ-002 therefore remain blocked for long-running filesystem server executables until streaming ELF mapping is attached to the canonical process manager/scheduler lifecycle with a real PID, wait/exit status, cancellation, address-space reclamation, and restart accounting. `FsExecReceipt` reports `pid == 0` for the current synchronous streaming path and preserves its exit code honestly.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
