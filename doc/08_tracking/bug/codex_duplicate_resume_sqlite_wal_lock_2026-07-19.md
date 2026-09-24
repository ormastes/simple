# Codex duplicate resume SQLite/WAL contention
## Closed 2026-09-16 — Status FIXED; stale duplicate stopped, checkpoints ok, flock guard added

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** FIXED
**Severity:** P1 — duplicate writers could contend on one session and retain WAL state

## Evidence

Session `019f4f6d-2a14-7532-a73a-5dda22da99cc` was simultaneously owned by
two `codex resume` process trees. The older completed instance remained alive
for more than 37 hours while holding `logs_2.sqlite` and its WAL open. The log
WAL had grown to 586 MB.

The stale duplicate was stopped. Passive and truncate checkpoints completed
with no busy pages; new immediate write transactions succeeded for logs,
state, and goals databases; state/goals quick checks returned `ok`.

## Prevention

The repo Codex launcher now resolves an explicit resume ID to its rollout and
takes a nonblocking `flock` on that rollout before launching Codex. A concurrent
guarded resume exits 4 without reaching Codex. It also refuses a launch when a
legacy/direct Codex process is already resuming the same ID. Ownership releases
automatically after the owning process tree exits, and different sessions
remain independent.

Direct invocations that bypass `bin/codex` cannot be protected by this repo
guard; keep repo `bin/` first on `PATH` as required by `AGENTS.md`.

