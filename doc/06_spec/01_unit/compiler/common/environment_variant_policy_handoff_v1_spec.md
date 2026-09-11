# Environment variant policy handoff V1

This manual covers the pure, fixed-order policy wire passed from a native-build
parent to its worker.

## Roundtrip

1. Build policy inputs with distinct CLI, environment, and administrator data.
2. Resolve the policy and encode it into the bounded base64url argument value.
3. Decode it and compare policy digest, target CPU, target features, and every
   selected input field.
4. Re-encode the decoded value and require byte-identical canonical output.

Expected result: the worker observes exactly the policy and target inputs the
parent collected.

## Rejection cases

Mutation, padded/noncanonical base64url, an argument over 22,000 bytes, an
invalid policy, or a digest mismatch is rejected before a worker can use the
value. The integrity digest proves only that the wire is intact; it is not
administrator authority.

## Cache identity

Changing effective policy or generated target feature inputs changes the warm
artifact identity. Target-codegen options remain separate from host policy.

