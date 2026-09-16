# SimpleOS streaming exec has no registered process identity
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

The x86_64 raw-ELF streaming handoff runs synchronously and returns the program exit code, but it does not create a scheduler-owned task/process record. A PID must not be allocated solely for logging or receipts because no process with that identity exists.

REQ-001/REQ-002 therefore remain blocked for long-running filesystem server executables until streaming ELF mapping is attached to the canonical process manager/scheduler lifecycle with a real PID, wait/exit status, cancellation, address-space reclamation, and restart accounting. `FsExecReceipt` reports `pid == 0` for the current synchronous streaming path and preserves its exit code honestly.

