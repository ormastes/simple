# C34 explicit Some payload metadata and nominal nil comparisons

Source evidence: frozen C34 `20a93224b3f08a86a15b520252bd95965f1e6423`,
producer `f00dbc9c608dfaf22a15736747799821ed1b75871bf45ad3fe1b133701030e81`.
Retained native diagnostics:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c34-producer-mir-json-fragments-attempt1/normalized-mir-errors.json`
and `mir-error-groups.json`. The attempt failed; no serializer qualification
or memory improvement is claimed.

Six enum payload errors occur at `hir_types.spl:797` (`DimExprKind.Named`)
and `mir_data.spl:603,643,665,668,683` (`Intrinsic`, `CallTerminator`, `Call`).
Every rejected argument is an explicit `Some` around a scalar or nominal
record for an optional declared field. `lower_enum_construct_named` builds
the canonical Option handle but previously recorded only presence/transport
metadata, not its `Optional(inner)` HIR type. Strict declared-slot validation
correctly refuses to infer that type from an opaque enum carrier.

The repair retains the actual payload's known local/expression type on the
constructed Some result. Primitive literals use the existing guarded
`option_map_value_hir_type` recovery before payload boxing/float bitcasts.
No expected slot type is assigned to an unverified payload, constructor
arguments are still evaluated once, and enum validation is unchanged.
Unknown payloads remain unproven; wrong primitive/nominal payloads and raw
integer carriers remain rejected. The runtime handle layout is unchanged.

Three separate errors at `mir_types.spl:360,403` and `mir_json.spl:612` route
`MirType == nil` into struct operator lookup. Historical bootstrap record
slots can hold nil despite nominal declarations. The existing nil-presence
branch now also recognizes the operand's actual `MirTypeKind.Struct` local,
only for Eq/NotEq with exactly one literal nil. It calls the existing
`rt_is_none`/`rt_is_some` predicates; ordinary struct-to-struct operators are
unchanged, and scalar payload bits (notably integer 3) retain their separate
typed handling.

This is justified by the current MIR ABI, not an assumption about arbitrary
native value layouts: `llvm_type_mapper.spl:271–280` documents Struct as a
SymbolId-owned pointer-passed aggregate, consistent with the existing
struct-operator path in `expr_dispatch.spl`. `simple_core/core_values.spl:293`
recognizes the nil sentinel and canonical Option absence; other values are
present. This patch does not introduce aggregate field reads or invoke a
record's user equality method to test presence.

Authored coverage:

- `optional_enum_payload_owner_spec.spl`: real frontend/HIR/MIR lowering,
  actual scalar and nominal Some owners, mismatched primitive/nominal owners,
  raw integer optional carrier rejection, mandatory-slot rejection and nil
  comparisons without a struct equality implementation.
- `enum_optional_some/main.spl`: native execution oracle for 3, 0, negative
  values, nominal optional payloads and nil; expected exit 0.
- `enum_optional_some/negative_owner.spl`: must fail compilation with payload
  mismatch and no artifact, despite identical record layouts.
- `native_struct_nil_presence/main.spl`: both comparison orders, actual nil
  and present nominal records, optional records, scalar 3, and ordinary
  overloaded record equality; expected exit 0.

Run native entries through an admitted matching producer/capsule with private
source-bound caches and explicit entry closure. No build or runtime tests
were run for this source-only repair. Independent review and coordinated
qualification remain required. The other C34 MIR error groups, including
coalesce result ownership and imported struct patterns, remain separate.
