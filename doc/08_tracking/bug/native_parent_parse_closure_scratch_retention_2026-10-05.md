# Parent retains entry-closure preparation while native workers run

Status: source repair prepared; native behavior, live allocations, and peak RSS
are **UNVERIFIED**. This is not a passing bootstrap or a measured 2 GiB saving.

The `early-p4-full-cli-918498-cfa73` run used producer
`cfa73ac440cd4fc1d0671610d3d8493b267aab4ecfa46612db2e95b5d99f0bdd`
(703 lifetime repair), target source `918498b2b185a4026c4313bc7ba0cea774f107a4`.
It ended with RSS exit 88, peak 6,838,908 KiB above enforced 6,835,937 KiB,
quiescent=1 and observer_errors=0. Last HIR progress was 2,589/2,592, with
zero source failures. The parent retained approximately 1.98 GB while its
worker reached approximately 5 GB; these process observations do not assign
every byte to a specific allocation owner.

The 703 shard transaction no longer retains completed full HIR modules.
Its phase-wide memo values are indices, names, and name collections, not full
HirModule bodies. A separate parent path still opened and validated the source
inventory, walked the entire entry closure, and published selection/request
files outside any scratch scope. Dropping lexical locals or replacing the
source-scan cache dictionaries does not reclaim their native no-GC allocation
graphs. They survived while the parent waited for parse/HIR/final workers.

## Repair and retained-owner audit

`native_build_parse_closure_owner.spl` scopes only this parent publication.
It leaves source authentication, aliases, entry roots, producer/policy digests,
exclusive receipt writes and worker revalidation intact. A four-field result
(request path, digest, selected count, error) is promoted; the OS environment
permission is published only after successful reclamation. Errors use the same
cleanup path and leave no request permission. A nested scope is refused without
ending the caller's scope. An active compiler epoch is refused.

Reachable mutable owners audited:

| Owner | Treatment |
|---|---|
| `driver_source_loading` three scan dictionaries | Replace without traversing old data before end; retain scalar diagnostic counters |
| `native_build_closure` six SCV memo strings | Clear before end; next walk reopens inherited authority |
| `host_path` lazy platform array | Clear before end through its defining owner; recompute platform on next use |
| `driver_admitted_epoch` semantic maps | No active epoch permitted; no mutation by this parent walk |
| SCV inventory/snapshot/open, source authority, selection/request codec | No mutable heap-global result owner in the traced read/publication path |
| Warm candidate publication | Durable file write only; no retained in-memory candidate |
| Environment facade/runtime | No Simple heap cache; `_putenv_s`/`setenv` copies bytes before temporary C strings are freed |
| File/hash/text helpers | Return local managed values; no mutable heap-global memo; host-path cache handled above |

The initial cold SCV acquisition is intentionally outside this scope: snapshot
materialization already uses per-file transient scopes and cannot be nested.
Its retained inventory cost and the final worker's own peak remain separate
limitations. No cap, source identity, module count or failure gate is relaxed.

## Native verification recipe (pending)

Compile `test/04_smoke/native_parent_parse_closure_scope.spl` with a rebuilt
producer containing this repair and the authenticated runtime. Use the ordinary
owned native-build recipe with 80 codegen jobs, bounded frontend, independent
cache lease and resource admission. Retain compiler/source/runtime receipts.
Then run `native_parent_parse_closure_scope_test.py` with the actual executable,
its SHA-256 and a private evidence parent, under the existing owned Job collector.

The native fixture creates a real two-file Git/SCV source authority. It checks
cold/warm identical closure records after reclamation, original request and
source-byte revalidation, actual heap-registry reduction against an unscoped
walk, existing-file publication failure, invalid authority, successful recovery,
and nested-scope refusal without stealing the caller's ownership. It preserves
all files/logs and reports real nonzero counts. No source assertion substitutes
for allocation evidence.

Finally compare matched cold and warm full native-build parent/worker RSS using
the same target, cache state and resource policy. The failed original cohort and
caches remain untouched; do not restart an unchanged producer or assert the
remaining worker peak is fixed by this change.
