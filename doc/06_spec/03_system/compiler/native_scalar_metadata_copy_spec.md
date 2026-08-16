# Native scalar metadata-copy regression

## Purpose

REQ-BST-META-001 verifies that staged-native compiler metadata copies keep the
aggregate value inside its owning parallel arrays and transport only scalar
source/destination IDs across the helper boundary.

## Prerequisites

Use the exact admitted Stage-2 binary and its passing sanity receipt. Rust-seed,
symlinked, stale, hash-mismatched, or unsupported-stage tools fail closed.

## Procedure

1. Confirm the production array-copy path calls the source-first scalar helper.
2. Compile the isolated fixture with fallback disabled and an isolated cache.
3. Execute the newly produced candidate and inspect its exact verdict.

## Expected evidence

The executable scenario checks append and update behavior, the missing-source
no-op, both isolation and resource states, candidate existence, exact compiler
hash, and exact native output.

## Failure handling

Any missing provenance, source wiring, build output, executable, verdict, or
zero exit fails the scenario. Never reuse a stale candidate.

## Traceability

REQ-BST-META-001 maps to the production helper, unit source contract,
pure-Simple native fixture, integration wrapper, and system scenario.

## Artifacts

Build and run logs are retained under
`build/test-artifacts/native_scalar_metadata_copy/`.

## Limitations

This is Stage-2-scoped compiler regression evidence only. It does not admit
Stage 3/4 or prove the SimpleOS deployment image and desktop boot plan.

Executable source: `test/03_system/compiler/native_scalar_metadata_copy_spec.spl`.
