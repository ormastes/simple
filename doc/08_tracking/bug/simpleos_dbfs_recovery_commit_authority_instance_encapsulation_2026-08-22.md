# DBFS recovery/commit authority lacks sealed instance construction

## Blocker

`device_commit_owner.spl` owns the canonical mutex and durable DBFS state, but
its compatibility surface exports scalar `inst_id` recovery, persistence,
flush, transaction, and locked operations. `DbFsDriver.open_on_device` also
registers an instance without returning a language-opaque owner handle. Adding
an optional one-shot token beside those paths would therefore not prove that a
server-data instance has exactly one recovery/commit authority: an importer
could bypass it through the legacy scalar surface, while a public token issuer
keyed only by a guessed `inst_id` could target another owner's registration.

The attempted token implementation was reverted. No server-data namespace
owner may claim sealed recovery or durable commit until construction of that
specific DBFS instance returns an opaque owner-held port and all scalar
recovery/commit operations are package-private or friend-limited behind it.

The 2026-08-22 visibility follow-up also found that the compiler cannot yet
enforce that boundary. `OutlineModule` retains `friends` and
`internal_exports`, but `ParserModule` and `ModuleSurface` discard them before
HIR import resolution. Imported field metadata likewise drops member
visibility and declaring-owner identity. Phase 2 must carry those authorities
through the frontend, resolve a re-export to its terminal declaration, and use
one shared scope predicate for Public, Private, Package, Internal+friend, Up,
and Peer. That predicate should consult one frozen indexed declaration table;
repeated linear surface scans are not acceptable on the import hot path.

## Required acceptance evidence

- Compile-negative tests prove external code cannot construct, inspect, or
  mutate the owner handle or one-shot capability and cannot import scalar
  persist/flush/locked entrypoints.
- Positive and negative visibility tests cover friends, internal exports,
  package/up/peer scopes, re-export aliases, fields, and constructors through
  check, interpreter, and native compilation without fallback execution.
- Behavioral tests cover forged owner/capability values, replay-first failure,
  copied-token races, slot reuse, unregister invalidation, stale generation,
  capacity and nonce exhaustion, and every recovery/write/flush failure.
- One registered server-data instance permits at most one live recovery token;
  unregister atomically invalidates the owner and outstanding tokens under the
  existing DBFS mutex.
- Legacy non-server DBFS behavior remains compatible, while scans prove no raw
  device, driver, instance ID, or commit port escapes the server-data owner.

## Performance bounds

Use bounded tables (at most 64 owners and 256 live/terminal token slots), O(1)
token consume, and at most one bounded O(256) scan on issue/unregister. Commit
must add no payload copy or per-byte dispatch. With an admitted self-hosted
runtime, compare the same recovery plus 1,000 x 4 KiB commit workload before
and after, report wall time and peak RSS/allocation evidence, run the Simple
optimizer on touched `.spl` hot paths, and reject an unexplained regression
above 5% or peak RSS growth above 4 MiB.
