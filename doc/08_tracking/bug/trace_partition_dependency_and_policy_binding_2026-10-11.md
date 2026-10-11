# Pending trace partition dependency and policy binding repairs

Status: open; independent source review, no native verification.

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
