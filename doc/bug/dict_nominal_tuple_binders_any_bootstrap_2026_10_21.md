# Typed dictionary tuple binders lose nominal types during bootstrap

Canonical ID: `dict_nominal_tuple_binders_any_bootstrap_2026_10_21`
Status: open; typed-local bootstrap workaround, root inference repair pending.
Bug DB reconciliation: pending a qualified self-hosted DB command; the Rust
seed is used only for bootstrap diagnostics and cannot provide that admission.

## Producer and failure

Source `0bfa8039acd`, Windows LLVM Phase 2, Rust bootstrap seed SHA-256
`32014B3401E3CB76AEC44ACB475A22F2385FEFCD1D19AB71049E52D633356825`.
Producer path in the frozen parent tree:
`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe`.
Canonical `stage2-native-build.log` records 1431 compiled and five failed
modules, including these three dictionary tuple-binder failures:

- `enum_pattern_physical_v1.spl`: `EnumPatternPhysicalCheckerV1.validate`,
  erased `site.instruction_index`.
- `enum_semantic_identity_v1.spl`: `enum_semantic_declaration_identity_v1`,
  erased `key.id`.
- `enum_semantic_validation_v1.spl`: `EnumPhysicalValidatorV1.preflight`,
  erased `declaration.symbol`.

Rust `TypeRegistry::get_iterable_element` omits `HirType::Dict`. Tuple-for
lowering consequently registers both binders as `ANY`. Receiver-blind field
lookup can conceal this when a field has only one candidate layout; with
conflicting nominal layouts it correctly rejects an unsafe guessed access.
Pure-Simple tuple-for HIR lowering also currently records nil binder types.

## Scoped workaround and retirement

Keep dictionary iteration order, keys, values, work charging, errors and
validation unchanged. Bind explicit nominal typed locals immediately inside
the affected loops, including the next declarations loop in preflight. This
restores existing declared dictionary K/V types without inferring layouts by
field names. Each block carries this canonical ID and the recovery revision.
The workaround commit is the Git commit introducing these linked blocks.

Root-fix owner: compiler dictionary-iterable/tuple-binder typing (deferred by
the merge owner to preserve the successful canonical objects). Remove only
after a rebuilt admitted producer compiles and executes the original fixture
with conflicting nominal layouts and the original enum modules without the
typed locals. Do not treat this source workaround as an inference fix.

## Diagnostic evidence

Private evidence: `build/session/enum-dict-any/`. The initial single-layout
control compiled and ran to 31, exposing why that control alone was weak.
Adding conflicting `id`, `symbol`, and `instruction_index` layouts reproduces
the exact `ANY.id` failure. The retained original fixture is
`test/fixtures/native_dict_nominal_loop/main.spl`; positive typed-local and
affected-module verification results are recorded after execution.
No canonical source/cache writer or successful object was modified.
