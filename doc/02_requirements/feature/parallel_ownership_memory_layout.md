# Parallel Ownership and Storage Layout Requirements

Status: selected from the user-provided 2026-08-12 architecture brief.

## Functional requirements

- REQ-PAR-001: `T[]` remains a logical collection interface regardless of selected AoS, SoA, AoSoA, grouped, tiled, packed, or external-fixed storage.
- REQ-PAR-002: Safe cross-domain transfer classifies values as inline copy, frozen share, isolated move, object handle, encoded copy, synchronized share, or non-transferable.
- REQ-PAR-003: A child-created disconnected result transfers to its parent without a migration warning; a parent-owned mutable graph transfers down only through an explicit consuming move.
- REQ-PAR-004: A moved source is unusable after transfer. Joining, cancellation, timeout, or child failure does not restore the source binding.
- REQ-PAR-005: Safe process/actor/channel transport never carries a dereferenceable process-local pointer or unchecked dynamic heap graph.
- REQ-PAR-006: Safe public mailboxes are typed and bounded. Send and receive report disconnect, cancellation, and backpressure failures.
- REQ-PAR-007: Structured task groups permit temporary mutable loans only for proven-disjoint regions whose children join before the scope exits.
- REQ-PAR-008: Children create isolated update, patch, append, reduction, or shard output; the logical owner validates and commits canonical state.
- REQ-PAR-009: Commit validates base revision and declared writes, applies a declared conflict policy, and records a deterministic order whenever policy requires determinism.
- REQ-PAR-010: MDSOC stages expose transfer direction, access summary, layout plan, and commit policy through common contracts rather than sibling-private types.
- REQ-MEM-001: Storage lowering preserves field/index semantics and rejects automatic transformation of ABI, wire, persistence, MMIO, or address-observed representations.
- REQ-MEM-002: Layout selection is policy-driven and can choose a conservative reference representation when confidence is insufficient.
- REQ-MEM-003: Layout views are revision- and plan-hash-keyed; stale views are rejected and dependent views invalidate after mutation.
- REQ-MEM-004: False-sharing remediation prioritizes task-local accumulation and partitioning before padding.

## Acceptance mapping

| Requirement | Primary work package | Required evidence |
|---|---|---|
| REQ-PAR-001, REQ-MEM-001..003 | WP-02, WP-20..25 | semantic parity and ABI rejection tests |
| REQ-PAR-002..005 | WP-01, WP-10..13, WP-16..17 | transfer vectors, source diagnostics, process isolation |
| REQ-PAR-006..007 | WP-14, WP-18 | bounded/rendezvous and scoped-loan tests |
| REQ-PAR-008..009 | WP-03, WP-15 | deterministic replay and atomic-publish tests |
| REQ-PAR-010 | WP-30 | routed-stage receipt and bypass probe |
| REQ-MEM-004 | WP-26..27 | writer-set/allocator evidence |

## Focused parent-authoritative process traceability

The executable source
`test/03_system/feature/language/parent_commit_piped_result_spec.spl` and its
manual mirror
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`
map REQ-PAR-002, REQ-PAR-003, REQ-PAR-005, REQ-PAR-006, REQ-PAR-008, and
REQ-PAR-009 to real-child framing/replay, copied retention, typed parent
apply/verify, deterministic receipt, and rollback assertions. The source is
wired, but the mapping remains execution-blocked until an admitted pure-Simple
native verdict is retained; it is not a completion claim for the broader actor,
cancellation, or backpressure requirements.

The complementary Modern SSpec
`test/03_system/feature/language/actor_channel_authority_spec.spl` and authored
mirror
`doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md`
map the implemented scalar-text portion of REQ-PAR-002 and REQ-PAR-006 to one
scheduler-owned bounded mailbox/reply authority, copied argument retention,
finite backpressure, unknown/stopped rejection, unique terminal removal, and
fail-closed owner-domain query/reply lifecycle guards over populated state.
Coverage is partial: the owner-domain scenario injects an identity mismatch;
synchronized cross-thread ingress and typed heap/owned payload transport remain
open. Native execution remains TEST_BLOCKED because the admitted Stage-2
compiler has no qualified self-hosted test/docgen/maintenance surface.
