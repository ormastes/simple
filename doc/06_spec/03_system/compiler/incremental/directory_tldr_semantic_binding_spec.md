# Directory TLD Semantic Binding Contract

**Requirement:** REQ-CACHE-AOP-001
**Evidence class:** source-contract; bounded to package-init TLD serialization.
**Status:** Four authored scenarios; UNRUN. This is a manually authored acceptance manual, not generated execution evidence. Compiler checks, test execution, and SPipe doc generation were not performed.

## Purpose and scope

This contract checks that the package-init TLD codec retains and binds the directory's inherited parent context, membership root, aspect root, and ordered member identifiers. The fixture supplies valid SHA-256 digests for all required digest fields except in the explicit malformed-parent case.

These cases cover serialization and validation through `compiler.common.cache_contract.package_init_tld_v1`. They do not establish before-SRC publication, runtime behavior, cache invalidation, or any broader directory-TLD lifecycle property.

## Assumptions and preconditions

- The fixture calls the real package-init contract codec and validator.
- Valid fixture digests are produced by `std.common.crypto.sha256.sha256_text`.
- The encoded form is the byte array returned by `package_init_tld_encode_v1`; an invalid contract must encode as an empty byte array.
- No mocked owner, source scan, compiler execution, or runtime observation is part of this evidence.

## Acceptance scenarios

### 1. Preserve separate parent, membership, aspect, and ordered-member values

1. Bind inherited context and directory membership using distinct valid digests.
2. Decode the stored directory contract.
3. Require the decoded parent digest, membership root, aspect root, and ordered member list to match their original, distinct values.

### 2. Bind parent-context changes

1. Build two otherwise identical valid directory contracts with different parent-context digests.
2. Require their encoded byte arrays to differ.

### 3. Bind membership and aspect changes independently

1. Encode a valid baseline contract.
2. Change only the membership root and require the bytes to differ from baseline.
3. Change only the aspect root and require the bytes to differ from baseline.

### 4. Reject malformed inherited context

1. Supply a malformed parent digest while keeping the other required digests valid.
2. Require the contract validator to reject the value and the encoder to return an empty byte array.

## Verification and recovery

Execution remains UNRUN. When this contract is later executed, a failure should be investigated in the owner codec or fixture inputs; it must not be reinterpreted as evidence about publication order, runtime behavior, or invalidation. No passing or failing test result is claimed here.
