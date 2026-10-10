# Generic field prescan resolves parameters outside their declaration scope

The scalar DB native build failed HIR aggregation on
`src/lib/common/search/types.spl`: `unresolved type: Id`. Its valid
`PostingList<Id>` declaration contains `ids: [Id]`. The aggregate claimed
57 modules, stored 56, and failed one; the command exited 1 with peak RSS
2,247,712 KiB, below the 5,859,375 KiB enforced cap.

The producer was the qualified pure-Simple Phase2 compiler
`15a04a74f55062bed6767a9ebfc7a917035685b8a0f103144eb3e1673f09a86d`,
using app source `b646438a1827920940ec4dc671989517cde3965e` and native runtime
archive `6ca86625f7e19bf72eb7c086ca96e3138fbcca71a612d620630ded6bca8ed5b8`.
The original log and receipt are retained under
`D:/dev/simple/build/item5-scalar-apps-20261008/db/`.

## Cause and repair

`module_build.spl` calls `prescan_composite_field_types` before lowering
function bodies. That scan lowered every field annotation at module scope,
without the struct/class type parameters. Later full struct/class lowering
already binds those parameters in a temporary scope, but cannot undo the
earlier fatal diagnostic. The legacy single-uppercase-letter fallback can
hide this omission for `T`; `Id` correctly exposes it.

Pass the declaration's actual type parameters to the prescan, bind them in
a temporary class scope using the existing `lower_type_param`, and pop that
scope after field lowering. A scan-local symbol map emits canonical
`HirTypeKind.TypeParam(name, bounds)` for these binders: retaining temporary
`Named` symbol IDs would not match the later full declaration's parameter
IDs. Existing monomorphization substitutes canonical parameters by name.
Restore the map after the scan; do not alter ordinary named-type resolution.
Preserve field maps, real unknown-type errors,
and the existing non-emittable generic-template policy. This does not add
generic instantiation support or loosen unresolved-type admission.

## Regression and qualification

- `test/fixtures/compiler/generic_field_prescan.spl` declares an unused
  generic struct and class with multi-character parameters, and checks an
  ordinary concrete field read in its native entrypoint.
- `test/unit/compiler/hir/generic_field_prescan_spec.spl` checks successful
  scoped lowering, unknown field rejection, and no binder leakage into a
  sibling declaration, using the actual parser and HIR owner.
- Native negative fixtures `generic_field_prescan_unknown.spl` and
  `generic_field_prescan_sibling.spl` require HIR failures naming
  `MissingType` and `Id`, respectively. They must not publish an executable.

The isolated one-module baseline reproduced both unresolved `Id` and
`Element` diagnostics with compiler15a04: build exit 1, no executable,
peak 1,895,304 KiB, enforced cap 5,859,375 KiB, and quiescent receipt.
Evidence is retained under
`D:/dev/simple/build/item5-generic-field-prescan-20261008/baseline/`.
Compiler15a04 contains the prescan owner at ELF address `0x774d62`.
Its `bootstrap_main.spl:586` internal-worker route calls compiled native-build
functions directly, despite the coordinator's source-shaped `run` argument.
Changing the worker source does not replace this embedded HIR owner; a
coordinated compiler rebuild is required to qualify the repair. Symbol evidence
is retained in `embedded-owner-symbols.txt` beside the baseline directory.

The repaired compiler and regression sources have not yet executed.
The full DB app is not qualified. No frozen app source or shared build cache
was modified; the reviewed source patch awaits a coordinated compiler build.

## Static review and pending qualification

The sole `HirLowering(...)` constructor is in `hir_lowering/types.spl` and
initializes the new map empty. Prescan restores its previous map after popping
the declaration scope. Canonical parameter lookup is keyed by the freshly
bound symbol ID, so an unrelated same-spelled nominal type is not rewritten.
`monomorphize/type_subst.spl` substitutes `TypeParam(name, ...)` through its
name map. Function bodies can consume prescanned fields before full struct
lowering overwrites the cache; class fields retain the prescan cache. Both
therefore require canonical parameters rather than temporary `Named` IDs.
Ordinary full-declaration lowering and generic-template admission are unchanged.

This local commit is **UNQUALIFIED**, intended for the next coordinated
compiler build. Root reviewed the four-file source amendment with no P0/P1
finding. No repaired-compiler execution, instantiated-generic qualification,
or DB app pass is claimed. The native qualification recipe is retained at
`D:/dev/simple/build/review/item5-generic-field-prescan-qualify-20261008.sh`;
it requires a newly qualified compiler, positive native execution, and both
explicit HIR-negative diagnostics. Actual DB compilation remains a separate
required integration check after these focused results.
