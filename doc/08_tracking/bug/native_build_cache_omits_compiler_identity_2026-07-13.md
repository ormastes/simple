# Native-build cache omits compiler identity

## Symptom

After changing compiler lowering or code generation and bootstrapping a new
compiler, native-build can reuse unchanged module objects emitted by the old
compiler. SimpleOS compiler validation therefore requires an empty target cache
and recompiles all 617 modules (345-634 seconds observed).

## Owner evidence

- `src/compiler/80.driver/driver_build/incremental.spl` scopes and validates
  cache entries from module source/options/output existence, without compiler
  identity.
- `src/compiler/80.driver/driver_aot_output.spl` accepts those hits and records
  module fingerprints with empty dependency metadata.

## Required fix

Include a stable compiler/codegen identity in the cache scope or entry
fingerprint. A newly bootstrapped compiler must invalidate objects produced by
an older compiler, while repeated builds with the same compiler retain hits.

## Regression gate

Build one fixture into a cache, change the compiler identity while leaving the
fixture unchanged, and require a miss; repeat with the same identity and
require a hit.
