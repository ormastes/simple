# Macro and generic reverse-reference lifecycle

Status: implementation contract; runtime qualification UNRUN. This refines the
existing cache-with-SCV plan, not a second cache or authority. Owner: Astra
design/review; Luna implementation; root integrates. Compiler diagnostic budget
is exhausted: no build, native execution, seed fallback or passing test claim.

## Existing callers and ownership

- `driver_build/incremental.spl` builds, publishes and consumes reverse receipts
  for dependency invalidation. Its interface-hash cutoff currently drops
  macro/generic body-sensitive users; this is a production correctness defect.
- `cache/generic_spec_rr_producer_v1.spl` projects sealed generic manifests;
  `generic_specialization_list_v1.spl` owns the existing mono-derived outgoing
  producer. Text scanning cannot establish complete use inventory.
- `cache/reverse_reference_projection_v2.spl` owns inversion and replay;
  `reverse_reference_receipt.spl` owns legacy text receipt persistence.
- `cache/reference/reverse_reference_coordinator_v1.spl` owns binary shard
  persistence through verified CAS; `reverse_reference_atomic_generation_v2`
  and the existing action-root journal own generation transition contracts.
  Their unavailable live-authority gates remain closed until actual authority
  wiring exists; a caller-created digest does not establish authority.

RR lane may extend these owners and narrowly scoped versioned projection/demand
contracts. It must not edit the TLDR AsyncRef worker or standalone monomorphization
removal lane. Generic planner caller ownership is coordinated with that lane.

## Frozen data and failure contract

Committed complete forward manifests are the only dependency authority. A
projection is bound to exact logical scope, latest pinned forward root, canonical
consumer inventory and versioned schema. Use identity includes consumer, stable
site, producer/instance variant and activation/resolution/target context. Store
unique use sets; derive use and distinct-consumer counts separately. Request
counts, repeated loads and replay do not change demand.

Replacing a committed consumer manifest removes its old exact contributions and
adds its new exact contributions. Deletion and rename take effect only in a
committed complete inventory. A failed producer cannot delete historical edges;
that history is not evidence that the new projection is complete. Zero current
uses removes the scoped demand row, never a pinned artifact or historical root.

Missing, stale, partial, corrupt, generation-conflicting or failed publication
returns Unknown/NeedsFullRecheck. Recovery enumerates ALL consumers from the
latest pinned authoritative forward root and rebuilds the entire canonical
inversion, including removals and counts. Root change restarts boundedly, then
falls back to the whole affected scope. No subset repair may be admitted as exact.

All writes use existing SOSIX/storage publication owners. SOSIX text atomic
replacement alone does not provide expected-old-root fencing or parent-directory
durability. Existing binary staging requires a lease and absent destination; it
is not replacement CAS. If those stronger capabilities cannot be established,
production admission remains Unknown. A post-commit durability error does not
prove rollback: reconcile the journal before deciding the current root.

## Production behavior

Macro body changes reexpand recorded SRC users even when the provider interface
hash is unchanged. Generated-interface comparison after reexpansion may stop
downstream invalidation. Nested users and negative resolution candidates are
dependencies; unrelated users remain untouched only with complete evidence.
Authored source is never rewritten. Incoming churn never rewrites provider TLDR.

Generic inversion feeds the existing demand planner: canonical arguments,
template facet, resolution/target context, variant and need flags (Interface,
Const, Inline, AddressableCode, Export). Interface-only demand does not emit OBJ;
valid instances are reused; newly discovered body dependencies reach closure
before link seal. Count changes alone cannot authorize deleting pinned artifacts.

## Evidence and review

Unit/integration/acceptance sources cover 3,000 unique logical users, replay,
increment/decrement, last removal, pinned history, failed/deleted producers,
macro body/nested/negative candidate changes, generic target/need differences,
corruption, crash/stale writer and whole-scope recovery. Producer-derived oracles
must drive real invalidation/demand entrypoints. Sequential projection tests are
not native concurrency qualification. All execution remains UNRUN until a newly
qualified CLI is available. Frozen manual helpers, when needed:
`setup_rr_forward_scope_v3`, `check_rr_users_v3`, `check_rr_unknown_scope_v3` and
`step("...")`; no placeholder passes. Astra reviews source and limitations before
root integration; missing live authority blocks an end-to-end completion claim.
