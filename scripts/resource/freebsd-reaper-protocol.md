# FreeBSD reaper protocol v1 (candidate, not validated)

Private inherited pipes connect the Perl guard to `bootstrap-session-exec
--reaper-owner READ_FD WRITE_FD OBSERVATION_BUDGET_MS -- COMMAND...`. Workload stdin/stdout/stderr remain
unchanged. The owner closes control descriptors in the blocked payload before
exec; the parent closes opposite endpoints. No environment-selected control FD.

The native owner acquires reaper status before forking a payload blocked behind
an internal gate. It stays alive after payload exit. Parent requests are single
bytes: `S` sample, `G` release payload, `T` signal all descendants TERM, `Q` kill,
reap and finish. G has no response; T replies `TERM 1`. Duplicate G is invalid.

S replies `SAMPLE 1 OWNER PAYLOAD RAW_STATUS COUNT`, followed by COUNT rows:
`PID PPID PGID SID RSS_KIB ZOMBIE START_SECONDS START_MICROSECONDS`, then `END`.
RAW_STATUS is -1 while the payload is running; otherwise it is its wait status.
Rows include the owner. COUNT is at most 16385; depth at most 64; line length at
most 256 bytes. Counts, IDs, status and timestamps are decimal. Incomplete native
observation emits no successful frame and triggers cleanup/nonzero guard outcome.

Q replies `QUIET 1 RAW_STATUS OWNER START_SECONDS START_MICROSECONDS` only after
all owned descendants are reaped and absent. Owner then exits 0. Failed cleanup
replies with the same fields and QUIET 0. The failed-cleanup owner retains
ownership, closes the broken control channel,
and retries bounded cleanup attempts no more often than once per five-second
cooldown. It never voluntarily exits with unresolved descendants. The parent
reports non-quiescence plus its exact owner identity/reservation; missing helper
alone proves nothing. Parent EOF/death does not remove this reservation.
The parent releases `reaper_reservation_retained` only after a matching QUIET 1
and a zero native-owner exit. EOF, invalid reply, failed wait, or nonzero owner
exit retains the unresolved reservation even when that owner is already gone.
`reaper_owner_wait_status` records the actual native owner's raw wait status;
-1 means it was not reaped. This is separate from the payload's RAW_STATUS.

Terminal failures can send `ERROR 1 OWNER PHASE STAGE PID ERRNO ATTEMPTS SIGNAL
QUIET RAW_STATUS` on the private reply pipe. PHASE is sample or stop; PID is the
affected process for sample failures and current parent for stop failures.
QUIET is -1 before cleanup, otherwise 0 or 1. The parent rejects the failed
observation and records the diagnostic. This is one atomic nonblocking write of
at most 255 bytes, with no retry: a full or broken pipe may lose it, but cannot
delay cleanup. Inherited stderr is never used for these diagnostics. A partial
prior sample remains a failure, never a recoverable frame. Diagnostics alone
do not prove a particular reparenting race without a captured failing stage.

Perl owns RSS summation/caps, normal timeout, signal grace and receipts. Native
code owns kernel queries, bounded protocol service, orphan reaping, and cleanup
on channel loss/parent death/signals. Each sample has the existing observation
budget; native cleanup is bounded to 2 seconds, protocol finalization to 3.
SIGKILL of owner cannot guarantee cleanup and must be reported unverified.

FreeBSD VM read-only confirmation: 14.4-RELEASE, kernel 1404000; sys/procctl.h
provides ACQUIRE/STATUS/GETPIDS/KILL/PDEATHSIG and nested-reaper flags. This does
not certify uninspected kernel fixes or runtime behavior.

Snapshot attempts drain waitable children before constructing a fresh frame,
using the existing 256-wait / 2-ms bound within the unchanged observation
deadline and three-attempt limit. The drain records payload wait status through
the same path as ordinary command servicing. No partial frame survives a retry.
An identity-confirmed nested owner whose metadata reports SZOMB fails with
`owner-zombie-unreaped`; it is not omitted from traversal. FreeBSD 14.4 excludes
zombies from procctl's PID lookup, while a zombie reaper can retain descendants
until its parent reaps it. This helper cannot reap another live parent's child;
that unresolved branch continues to fail closed.
