# Semantic canonical persistent owner

Source: `test/01_unit/compiler/cache/semantic_canonical_owner_spec.spl`.
Trace: REQ-CSM-003/006. Manual intent; native execution/docgen **UNRUN**.

1. Observe the original receiver's 82-byte header and 450-unit charge; retain
   cumulative counters and child state through successive calls.
2. Exceed byte, item and work quotas on the second operation. Preserve admitted
   counters and the first error through subsequent mutation/close/finalization.
3. Close two nested options, attach child to parent, and publish exactly one
   root matching the fixed independent 86-byte digest.
4. Reject a second root, repeated finish and late writes on their original owners.

Once a runtime is admitted, run `<runtime> test <spec> --native` and generate
`<runtime> spipe-docgen <spec> --output doc/06_spec --no-index`. Require zero
stubs. External digest calculations validate oracles, not execution.
