# Native worker macro forward transport and generic demand identities

Base: explicitly fetched release/1.0.0 commit
`5ca148fd6cdb33bf4fbb07dcabf52fa9e997ade7`. Owner: Astra design/review,
Luna implementation, root integration. This is a new production-transport
slice following the landed RR fail-closed fixes, not their reimplementation.

## Existing production route

`native_build_main.run_file_worker_pool_v1` invokes
`file_worker_inc_prepare_v1` before worker reuse and
`file_worker_inc_finish_v1` after successful worker completion. The existing
incremental owner stages `pending`; `file_worker_inc_commit_v1` promotes that
forward inventory only after successful linking. Its current rows describe
source/interface/import/object identities but omit macro outgoing evidence.

`native_build_main.prelink_generic_instances_v1` reads ordered inventory
module paths, derives generic lists and body-key lists, then calls
`prelink_instances_run_v1` without those paths. Consequently the previously
landed distinct-consumer helper is not connected to this actual planner call.

## Frozen scope

Extend the existing versioned forward manifest, its preparation/commit owner,
and these narrow native coordinator callsites. A small macro transport module
may own validation and pure candidate selection. No parallel database,
scheduler, journal or publication authority is introduced. Provider TLDR
retains outgoing information only. Do not modify formal-bound RR inversion
semantics or open closed namespace/native capability gates.

Macro snapshot data must originate from the actual parser/resolver-produced
macro tables. Bind source identity and source digest to that data, rejecting
missing, malformed, duplicate, foreign or partial evidence. Explicit empty
outgoing data differs from failed/unavailable data. Old-version manifests
migrate to Unknown macro evidence; they cannot prove empty dependencies.
Failed compilation/link/publication cannot replace prior committed inventory.
Renames/deletions take effect only through the successful complete replacement.

Candidate invalidation is advisory and additive: it may add rebuild work but
cannot authorize a cache hit, zero users, or an exact reverse projection.
Incomplete source-generation binding, unresolved candidate membership, missing
scope entries or publication doubt widens to the complete affected source
scope. Never substitute a guessed path/definition mapping or regex-derived
macro inventory. A source-fresh companion alone is not journal authority.
No `.rr` writes are added: use the existing namespace/SOSIX owner if a future
admitted publication becomes available. Atomic text visibility alone does not
establish expected-root fencing or parent-directory durability.

The native app already admits immutable SCV source authority before spawning
workers. Reuse `compiler_source_authority_open_published_v1` and
`compiler_source_authority_inventory_v1` at that app boundary: the latter reads
the exact inherited inventory generation and checks digest/count/membership.
Pass its existing source identities/content digests and snapshot binding into
the compiler owner; do not import the app into the compiler or mint an authority
from a caller-supplied digest. Exact worker-path mapping must be validated.
Unchanged prior rows alone cannot prove unchanged scope: a new source can alter
negative macro candidates. Missing scope admission disables reuse rather than
claiming a no-change hit. SCV source authority does not substitute for RR
namespace publication authority or a compiled-object generation witness.

For generic demand, transport module paths alongside body-key lists without
reordering or cardinality loss. Compute unique per-key consumer sets in the
actual prelink plan. Conflicting duplicate consumer records or missing
identity make demand incomplete. Preserve target/body-key identity and existing
object pin protection. Counts are distinct modules, not invocation counts.

## Acceptance evidence

Author focused tests for version migration, explicit empty versus failed,
foreign/corrupt snapshots, shared macro bodies with unchanged interfaces,
full-scope conservative fallback, no-change reuse, committed removal/rename,
replay deduplication and actual prelink identity/cardinality transport.
Use real parser/resolver output for the producer oracle. Source-only tests
remain UNRUN absent a newly qualified compiler. Native publication, concurrency,
durability and exact committed-root completeness are not inferred from model
tests or source availability. Review the final actual production call chain
before root integration; retain incomplete acceptance items explicitly.
