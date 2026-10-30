# Macro and generic reverse-reference production gap

**Date:** 2026-10-30
**Status:** Partial safe implementation; production admission and native acceptance remain unqualified.

## Implemented source behavior

- The existing macro-use table from the parser-backed TLDR companion can now be converted to the existing semantic forward-read manifests. Resolved definitions, name membership, negative name reads, and incomplete coverage flow through `macro_use_forward_read_manifest_v1` into the existing projection builder. Missing, stale, malformed, or mismatched macro-use tables remain unsealed.
- An unsealed forward manifest now rejects the candidate reverse projection. The prior receipt remains historical data; its edges cannot be mixed into a candidate generation whose family markers claim completeness.
- Source edits select macro-definition and macro-name resolution/absence families along with the legacy families. The live incremental receipt writer still emits schema V1, which has no macro family. A macro-family lookup therefore fails closed and widens to the complete BuildCache source inventory. Schema V2+ receipts also widen because this caller has no source-path-to-macro-key mapping. This can recompile unrelated sources after any edit; incremental precision is intentionally unavailable until the committed macro inventory is transported into this caller.
- Generic plans can report distinct consumers per canonical concrete key from the supplied fresh per-module `generic-spec` lists. Duplicate module rows are deduplicated; conflicting duplicate module lists or conflicting metadata for one concrete key make the result incomplete. This is a snapshot-derived distinct-module count, not invocation/use-site count or committed-root proof.
- Incomplete generic plans cannot retire old demand. A failed instance build or needed-inventory write does not replace the prior `needed` file. Removed demand is reported separately from artifact reclamation; cached object bytes remain because this caller has no pin/epoch authority.

## Remaining production blockers

1. `generic_spec_publish_rr_v1` has no production caller in the current driver tree. `incremental_rebuild_plan_generic_v1` likewise has no production caller. The new macro conversion is connected to the existing generic RR producer helper, not yet to the driver commit path.
2. The module companion's source freshness and caller-provided module path list do not prove a complete committed scope inventory or authoritative forward root. Exact-empty coverage and full-scope recovery cannot be admitted from those values alone.
3. The actual incremental caller at `driver_build/incremental.spl` publishes the legacy receipt through temp-file write and rename. It has no expected-generation CAS or confirmed parent-directory durability. The SOSIX atomic text facade does not supply those missing properties, and the atomic-generation owner's live publisher/old-outgoing gates remain closed.
4. Macro identity is keyed by scoped macro definition IDs and semantic profile, while the legacy incremental caller supplies changed source paths. The V1 schema lacks macro families, so changed private bodies conservatively fall back to all cache entries. No precise “unrelated user untouched” claim is made.
5. `generic-spec` retains canonical concrete keys and template/argument identity, but not invocation-site identities or need-interface/const/inline/addressable/export flags. Generic function/text fallback coverage may remain conservative. Demand counts here mean distinct module consumers only.
6. Old instance object reclamation requires a real pin/ownership cleanup path. This change retains orphaned cached bytes rather than deleting artifacts based only on the latest snapshot.

## Evidence status

Source regressions cover unsealed-manifest rejection, parser-produced macro forward reads, logical distinct-consumer aggregation (including 3,000 users), last-consumer demand removal, incomplete-scope no-drop behavior, and failed-run inventory retention. The 3,000-user case is a logical model, not concurrent compiler execution. Compiler builds, unit/integration specs, crash/fault tests, native publication gates, and warm-path measurements were not run in this worktree.
