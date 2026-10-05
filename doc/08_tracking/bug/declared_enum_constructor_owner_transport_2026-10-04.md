# Declared enum constructor owner transport

Status: source repair draft; every Simple/native regression below is UNRUN.

## Evidence and scope

The six-subsystem helper producer is SHA-256
`776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`,
source `9737d1217bc44439b56bba6c2ef16faaff51bd20`. The preserved full stderr
report `helper-full-diagnostics1/report.json` records 158 generator and 24
verdict MIR rows per backend; these are diagnostic rows, not independent bug
or test counts. This group includes undefined `WindowsProcessAdmissionV1`
and unresolved `Unknown`/`Started` constructors.

MIR MethodCall dispatch discards its static receiver owner and passes empty
scalar hints. The fallback can recover an enum only when its variant leaf is
globally unique. Explicit enum identity therefore disappears exactly when
another enum defines the same variant. Re-reading the nested receiver at that
MIR boundary has a documented native crash history; this repair does not
restore that fallback.

## Repair

HIR captures the resolved enum SymbolId before lowering arguments, preserves
selected static methods and local-variable shadowing, and classifies only
nongeneric positional constructors into the existing typed EnumLit node.
Named calls retain their old route. Generic declarations are recorded during
the existing enum prescan and retain their prior specialization route.
The prescan covers local enums and materialized `imported_enums` before bodies
(`module_build.spl`), plus materialized lexical enum imports
(`module_import_registration.spl`). Declaration-only imports need not enter
that inventory. A missing genericity row therefore also retains the old route;
absence is never treated as proof of a nongeneric declaration.

MIR stores payload types/names/kinds under the same qualified runtime owner as
variant discriminants. The checked constructor rejects missing owners,
unknown variants, wrong arity, and incompatible concrete payload types.
Arguments are evaluated once. Numeric widths are explicitly converted before
using the existing scalar or tuple carrier; nominal types require declaration
identity, not a method spelling or an arbitrary i64 carrier. Optional metadata
is extracted with the existing presence/projection pattern. Constructor and
match metadata use the same qualified key. The generic template path does not
compare unbound TypeParam metadata with already-specialized arguments.

All three order-independent prescan writers now retain the exact declaration
owner. A bare variant scan cannot collapse two declarations merely because
their discriminants match. True HirTypeKind.Result/Optional metadata retains
the intrinsic container owner; an identically spelled Named declaration does
not become a builtin. Legacy owner selection also checks collisions when a
bare fallback row exists in the qualified registry.

Typed and legacy nongeneric tuple writers share one encoding boundary:
floats use the existing widened-F64 bit representation, U64 uses the existing
wide unsigned box, and match restores each declared slot type. Both sides use
the same generic exclusion. Any adapts once before storage; a matched Any is
marked as an existing RuntimeValue so rewrapping cannot box it twice. Ambiguous
legacy multi-field owners and malformed payloads are fatal diagnostics.

New context maps have constructor/reset handling, MIR transient promotion
roots, and lifted-lambda metadata transport. No serialized HIR node or codec
schema changed. A source-bound rebuilt producer and normal cache invalidation
are required; old immutable caches are not stamped as compatible.

## Authored regression matrix

- `declared_enum_constructor_spec.spl`: direct HIR/MIR owner assertions for
  declared identity, static precedence, local shadowing, named and generic
  route exclusion, qualified payload signatures, unit/tuple arity, incompatible
  types, and numeric adaptation.
- `native_declared_enum_constructor.spl`: nine actual output checks, including
  colliding variant leaves, unit/tuple/text/class payloads and a shadowing local.
- `native_enum_numeric_payload_widths.spl`: thirteen signed/unsigned/narrow/wide
  integer, float, mixed tuple, scalar/tuple Any, cross-route, and Any rewrapping
  checks. Declared-order named calls exercise the existing legacy route.
- `enum_constructor_owners/main.spl`: six checks across same-named enums with
  different text/integer/class payloads, including returned and nested payloads
  in separate modules.
- `enum_constructor_wrong_arity.spl`, `enum_constructor_wrong_type.spl`, and
  `enum_constructor_unknown_variant.spl`: expected compile failures.
- `enum_constructor_generic_compatibility.spl`: integer/text generic enum
  compatibility fixture; `enum_constructor_generic_import/main.spl` covers the
  same types through an imported reexport. Existing generic support is not
  claimed qualified. The unit generic exclusion uses parsed declaration
  metadata and the real registration owner, rather than injecting the flag.

## Explicit remaining limits

`enum_constructor_named_pending.spl` preserves a reordered named-payload
oracle, and `enum_constructor_default_pending.spl` preserves the omitted
default-payload contract. Both are known unqualified follow-ups, not passing
tests. Struct-form EnumLit no longer silently emits a zero payload; its named
field binding requires a separate implementation. This checkpoint does not
claim to fix nullable-text narrowing or all imported Result method failures.
The authored numeric and aggregate carrier cases require actual native
execution before this repair is qualified.
