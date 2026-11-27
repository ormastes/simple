# Pending trace partition dependency and policy binding repairs

Status: closed 2026-11-06 (interpreter-verified; no native verification).

The pending semantic-partition implementation must not report a complete
incremental closure while omitting owners affected by global identity or
locator membership changes. Review found that raw changed paths and partition
declarations alone do not capture declaration-only locator changes or additions
and deletions of fallback artifact identities. Derive identity counts and
path-to-entity membership changes from both composed generations, including
negative lookups. Unknown dependency coverage remains incomplete.

The policy fingerprint must preserve semantic multiplicity. Identical repeated
convention or authority rows can change resolver diagnostics and authority
match counts; de-duplicating those rows before hashing can bind different
policies to the same identity. A caller-provided binding label does not validate
the actual policy payload or grant admission authority.

The partition composition path must retain cold-extractor diagnostic identity,
ordering, budget handling and early-return behavior. The equivalence oracle
must cover these branches and explicitly account for generation/provenance
fields. A comparison that omits changed semantics is insufficient.

Evidence: independent Astra review of the pending
`src/app/traceability/extract/snapshot_partitions.spl` implementation and its
relationship to `snapshot_facts.spl`. The implementation remains under repair;
this issue records findings rather than claiming a tested regression or fix.

## Resolution (2026-11-06)

Fixed in `src/app/traceability/extract/snapshot_partitions.spl`:
- invalidation unions base and candidate owners/dependency rows; identity
  signatures include declared locators (declaration-only locator moves);
  fallback identity add/delete and negative lookups flow through
  `changed_identity_keys`; an incomplete dependency inventory yields
  `full_rebuild: true, complete: false`.
- `update_trace_snapshot_partitions` recomputes the policy binding from the
  policy payload; duplicated rules produce a different binding.
- composition keeps decoded owners to their declared rows only and emits the
  registration diagnostics with the cold extractor's identity and order; the
  unreachable extra budget diagnostic was removed.

Evidence: `bin/simple.exe run test/01_unit/app/traceability/snapshot_partitions_spec.spl`
-> 16 examples, 0 failures (6 new; 3 failed before the fix: locator move,
incomplete report, cold diagnostic parity). Oracle covers malformed, missing
declaration and node-budget branches against `extract_snapshot_trace_facts_cold`.
