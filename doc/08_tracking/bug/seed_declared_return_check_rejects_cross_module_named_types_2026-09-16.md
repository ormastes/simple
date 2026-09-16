# Seed declared-return check rejects valid gradual-typing forms — 542 app files

**Status:** FIXED (validate_declared_return_type now compares semantically)

**Found:** 2026-09-16 ~13:20 local, full bootstrap chain9 on merged main
(810476a68a4), stage2 native-build: "542 file(s) failed to compile", every
failure `hir: Type mismatch: expected TypeId(N), found TypeId(M)` under the
Rust seed.

## Symptom

Any full bootstrap that rebuilds the Rust seed dies in stage 2: the seed
rejects 542 previously valid `src/app/**` files. Single-file repro with the
seed:

```
[jit-fallback] HIR lowering error: Type mismatch: expected TypeId(610),
found TypeId(614) [in src/app/cli/check_entry.spl]
```

## Cause

da8964fe990 (#1025, merged 2026-09-16 01:38 +0900, "native-struct verify
lane") added `validate_declared_return_type` to the Rust seed, comparing the
declared `-> T` annotation's TypeId against the trailing expression's TypeId
by RAW EQUALITY. TypeIds are module-registry-local (`HirModule` owns a
`TypeRegistry::new()`; `register` always allocates fresh ids), and the seed's
type system has several gradual-typing corners where the same logical type
legitimately carries different TypeIds. Raw equality therefore rejected
valid programs in five distinct shapes, observed live:

1. Cross-module / cross-registration named types (same nominal type,
   different registry ids; 542 files at once).
2. Dynamic `[T]` declaration vs fixed `[T; N]` literal.
3. Trailing `[]` empty literal (inference defaults element to i32).
4. Immutable `shared &T` returned where `T` is declared (value-transparent
   references from shared receivers; the self-hosted compiler and the
   interpreter both accept).
5. Trailing `nil` (the language's bottom literal).

The same squash also left 14 failing `hir::lower` tests; those failures were
symptoms of the same strictness (all 14 pass after this fix).

## Fix

`validate_declared_return_type` delegates to `hir_types_compatible`:
ANY/equal/NIL fast paths; numeric pairs; immutable shared references
interchangeable with their inner type (both directions); then a
registry-resolved structural comparison (named aggregates by NAME -- field
layouts legitimately differ between ANY-field fallback copies and
fully-typed declarations -- composites recursively; empty arrays admit any
array; dynamic array declarations admit any fixed size of a compatible
element). A TypeId that does not resolve in the module's own registry
belongs to another module's registry; module-local ids are meaningless
across registries, so those comparisons are admitted. The check's sound
scope is intra-module comparisons, which is also where the native-struct
return ABI risk it was added for lives.

Mismatch diagnostics are env-gated behind SIMPLE_SEED_RETURN_TYPE_DEBUG
(registry-resolved HirTypes plus the function name).

Verified: both declared-return unit tests pass (genuine `-> bool` returning
text still rejects); all 310 hir::lower tests pass (14 previously failing,
0 newly failing); the seed rebuilt with the fix type-checks ALL 542
originally failing files with zero Type mismatch diagnostics.

## Consequence

CI did not catch the regression because no CI job runs the full bootstrap
closure with a rebuilt seed. A dedicated multi-module import
re-registration unit fixture remains desirable; the full bootstrap closure
is the exercising case for now.
