# Builtin Array identity integration scenarios

Executable source:
`test/02_integration/compiler/collection_builtin_resolution_spec.spl`.
Requirements: collection planner REQ-002, REQ-003, REQ-007.
Manually authored companion; docgen and admitted execution remain pending.

1. Parse a real typed Array map source and resolve its HIR. Require a
   canonical ArrayMap identity, round-trip the module through the HIR codec,
   reject an old cache header, and inspect the emitted Array MIR loop.
2. Parse a named user receiver with a method called map. Require that it
   remains outside compiler builtin identity.
3. Execute resolved map/filter calls through the HIR interpreter. Require
   map result 5 and filtered result 2.

The latest Phase 1 diagnostic passes scenario 2. Scenario 1 reaches MIR
without lowering errors but fails because the serializer import is missing;
instruction assertions are unexecuted. Scenario 3 passes map and fails the
filter result shape. No production verification PASS is established.
