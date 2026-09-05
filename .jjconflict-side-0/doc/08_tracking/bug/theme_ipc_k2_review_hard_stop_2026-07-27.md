# Theme IPC K2 review hard stop

**Status:** open / fail-closed — re-verified against `origin/main` 2026-07-27,
still live  
**Iteration state:** three-cycle cap reached  
**Integration state:** K1 is landed; K2 candidates are rejected/unintegrated.
The three K2 shas below are **unrecoverable** — they were made in isolated
worktrees that were never pushed, and no longer resolve in either the git or
the jj object store. Do not attempt `git show` or a cherry-pick; the
fresh-lane resume contract below is the only path. See
[report](../../09_report/theme_hard_stops_unlanded_2026-07-27.md).

## Scope

K1 on `main` owns bounded copied IPC payloads and typed receive states without
claiming dispatcher authentication. A separate isolated K2 lane attempted to
add dispatcher-bound source identity, versioned syscall copy-in/copy-out,
retry-safe receive reservations, and complete caller migration:

- `235ef0250b` — K2 ABI/copy boundary;
- `41eedf1bf5` — nonblocking v1, single-CPU admission, reservations, and
  copyout planning;
- `d9554f91af` — broad caller migration, dispatcher ordering, mapping
  stability, and nonreusable reservation tokens.

None of the K2 commits was integrated or pushed. No admitted self-hosted runtime
was available; no executable syscall, service, SimpleOS, or QEMU PASS exists.
No full bootstrap or Rust seed was used.

## Candidate facts accepted statically

Final review found the series had implemented several source prerequisites:

- nonzero v1 receive timeout failed instead of returning false success;
- manager-owned reservation/rollback preserved queue order and accounting;
- SMP topology was intended to fail closed;
- K1 token exhaustion no longer wrapped/reused;
- copyout performed full-range planning/revalidation with progress checks;
- direct-env guards and the scoped ABI audit were green.

These are candidate-only facts, not landed behavior.

## Final rejection

The final candidate still had five P1 compatibility and entry-path gaps:

1. x86 compatibility syscall IDs 220/221 were emitted by user code but not
   registered by the installed x86 dispatcher, so they returned `ENOSYS`;
2. even if routed, x86 interrupt glue threaded mutable IPC/scheduler state only
   for IDs 20..23, so compatibility send/receive state would be discarded;
3. kernel-internal direct x86 syscall helpers bypassed LSTAR/SFMASK, while K2
   assumed every x86 entry had interrupts masked. Copyout mapping stability was
   therefore not guaranteed on every admitted path;
4. the C userlib dispatcher outside `src/**` still accepted the historical
   five-register layouts under raw IDs 20/21, but the new audit searched only
   `src/**`, so v0/v1 separation was incomplete;
5. broad migration used six-register v0 wrappers on RV32, whose `syscall6`
   implementation returns `ENOSYS`, regressing existing service callers.

Per the mandatory cap, there is no fourth K2 repair cycle.

## Fresh-lane resume contract

Start from current `origin/main` and retain landed K1:

1. define one cross-architecture ABI table covering x86_64, ARM64, RV64, and
   RV32, with explicit v0 compatibility and v1 IDs/layouts;
2. register every selected ID in the actual installed C/Simple/Rust dispatch
   paths and thread mutable manager/scheduler state for each;
3. make the caller audit cover `src`, `examples`, runtime C/Rust, generated
   syscall tables, and user libraries;
4. keep RV32 v0 on a supported five-register path or implement a real six-
   register path before migrating callers;
5. make copyout stability explicit for both hardware syscall entry and
   kernel-internal direct helpers by using a real shared interrupt/preemption/
   address-space stability owner, with restoration on every exit;
6. retain exact errno, timeout, reservation, token-exhaustion, pointer,
   capability, and zero-partial-write regressions;
7. obtain independent highest-capability review before integration.

Only after K2 lands may `ThemeChangedV1` receive a production OS transport.
