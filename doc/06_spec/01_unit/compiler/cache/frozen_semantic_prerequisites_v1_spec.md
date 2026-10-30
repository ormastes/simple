# Frozen semantic prerequisite diagnostics: authored manual

Source: `test/01_unit/compiler/cache/frozen_semantic_prerequisites_v1_spec.spl`.
Status: authored expected behavior; not generated or executed. This lane ran no builder, native test, compiler check or docgen.

1. Supply frozen bytes for a known i64 function returning 42 and an explicit target. Call the actual compiler-driver diagnostic API. Inspect real parse/HIR/HM counts, target decision receipt, observed HIR literal 42 and empty errors.
2. Supply parse-valid source declaring i64 but returning true. The actual HM Deny consumer must reject with real errors after parse and lowering. A syntax-only success is insufficient.
3. Observe true from actual bool HIR. Compile two functions, then another independent diagnostic run; retained observations must still match the original values and actual counts.
4. Try imports, attributes, generics, defaults, nested branches, externs, calls or additional statements outside the initial profile. Inspect explicit unsupported outcomes without semantic authorization.
5. Change frozen bytes without the matching SHA, exceed limits or metadata, use an invalid target, occupy the driver with another source or open a foreign scratch scope. The diagnostic API must refuse without stealing the existing owner.
6. Confirm every diagnostic keeps semantic and artifact authorization false. The five issuer admission and compiled-execution gates remain closed.

The initial profile is a vertical probe toward full semantic compilation. These assertions are not five-owner completion, sealed execution, code generation, cache admission, performance or publication evidence.
