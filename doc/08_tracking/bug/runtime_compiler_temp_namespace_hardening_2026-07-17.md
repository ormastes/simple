# Runtime compiler temporary namespace hardening
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Open risks

Runtime C objects use `simple_rt_<pid>_<raw-target>_<stem>.<ext>` paths. Two
hosted links for the same target running concurrently inside one process can
write and delete the same objects. Separate processes are PID-isolated, but PID
reuse can encounter stale files. The raw target text is also embedded directly
in the filename; current hosted-target admission narrows accepted values but a
future target surface must not permit path separators to escape the temp owner.

## Required prevention

Give every hosted link invocation its own deterministic staging directory or
nonce, and sanitize or hash the target component before creating paths. Add a
same-process parallel-link collision regression plus hostile target-component
tests. Do not treat tracking only the successfully created prefix as a fix: it
would leave the concurrent write collision intact.

This is intentionally separate from the landed early-error cleanup fix, which
correctly deletes the current full planned list but does not create the shared
namespace risk.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
