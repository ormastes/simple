# SCV warm inventory can reuse a stale snapshot after untracked source deletion

Status: IMPLEMENTED, UNVERIFIED — current-source runtime reproduction pending.

## Pre-fix failure path

1. A cold refresh admits an untracked `src/example.spl` through Git
   `ls-files --others` and publishes an inventory and compile snapshot.
2. The file is deleted outside SCV. No SCV event batch is guaranteed for an
   ordinary working-tree deletion.
3. A warm refresh asks `ls-files --others` again. A deleted untracked path is
   absent from that output, while `git diff --name-status HEAD` does not report
   it because it was never tracked. `compiler_inventory_git_events_v1` emits
   no delete event, so the inventory digest is unchanged.
4. `scv_compile_snapshot_acquire_v1` may find the existing destination for
   that digest and return `scv_compile_snapshot_open_v1`. The open path checks
   the stored receipt and stored snapshot inventory, but does not read the
   live source before reuse. The request can therefore compile the old bytes.

Relevant owners: `src/app/compiler_entrypoint/inventory_events.spl` and
`src/lib/scv/compile_snapshot.spl`. This is a static path analysis, not a
measured runtime failure. It must remain open until the integration case runs.

## Required fix

Persist a bounded, scope-bound digest of the *membership* of Git-visible
untracked compilable paths in the atomic inventory cursor. Each warm refresh
already requests the current untracked listing; compare its canonical path
digest against the admitted digest before snapshot reuse. On a membership
change, either emit exact deletion/create events from an immutable prior path
list or fail closed with an explicit cold-rebuild action. The cursor must bind
the source-root scope so a `src` request and a `src`+`test` request do not
cross-admit each other's membership. Migrate old cursors by cold rebuild.

The isolated source now publishes `simple-compile-event-cursor-v2` with
`untracked_src_digest` and `untracked_test_digest` in the same atomic CURRENT
record as the inventory digest. A warm request compares the digest for each
requested scope and fails with `untracked-membership-changed` when it differs;
an old v1 cursor requires explicit cold rebuild. This is a fail-closed
implementation, not an accepted fix until the integration and performance
cohorts pass on a current-source worker. It reuses the existing warm
`ls-files --others` listing, which may still traverse source roots; Target 6's
zero-scan hot-path gate remains open until an admitted event-maintained
membership source replaces that traversal.

Cold refresh now uses one tagged `git ls-files -t --cached --others` output to
derive both source events and untracked membership digests. This removes the
internal mismatch where two Git listings could observe different untracked
sets during one cold refresh. It does not freeze file contents or prevent a
directory change after the listing; current-source behavior and concurrent
writer admission still need proof.

Do not add a per-request stat/read of every inventory source as a shortcut:
that would hide a full warm source traversal and miss Target 6's latency/RSS
contract. Preserve the existing rule that an explicit cold rebuild derives a
complete inventory from the full Git listing without mutating Git or source.

## Acceptance case

In a disposable Git fixture, admit and snapshot an untracked `.spl` file,
delete it with no SCV journal event, then issue a warm request. The warm
request must reject or publish an inventory without the deleted identity; it
must never return the prior snapshot as admitted. A subsequent explicit cold
rebuild must remove the identity and admit the remaining sources. Repeat for
`src` and `test` scopes, and confirm a no-change warm request retains its
bounded time/RSS and zero dependency-source-open guarantees.
