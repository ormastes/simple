# C36 mono util migration contract (source-only proposal)

Issue: https://github.com/ormastes/simple/issues/3021

Owner: `compiler.frontend.parser_types_expr`, whose `Type` and `Expr` are
structs containing `TypeKind` and `ExprKind`, respectively. All util entrypoints
must inspect those fields, rather than match their wrapper structs as enums.
The standalone deferred import fix is commit
`b7d3da00e29787a229d1a5d721ccbe363a3681cf`.

| ConcreteType | Output TypeKind | Reverse rule |
|---|---|---|
| Int, Float, Bool, String, Nil | Named(canonical primitive name, []) | Preserve existing primitive aliases |
| Named(name) | Named(name, []) | Binding first, then primitive, then named |
| Array(inner) | Array(convert(inner), nil) | Ignore source array size as before |
| Tuple(items) | Tuple(convert each) | Convert each |
| Dict(key, value) | Named("Dict", [convert(key), convert(value)]) | Existing generic behavior yields Specialized("Dict", args) |
| Function(params, ret) | Function(convert params, convert ret) | Mandatory actual return type; no missing-return case |
| Optional(inner) | Optional(convert(inner)) | Convert inner |
| Union(items) | Union(convert each) | Preserve existing zero→Nil / one→member / many→Union rule |
| Specialized(name, args) | Named(name, []) | Preserve existing collapse to already-mangled name |

Synthetic output span: `Span(0, 0, 0, 0, "", 0)`, matching actual owner samples.
Input source spans never affected existing ConcreteType values.

| PointerKind | Actual TypeKind | Derived capability on reverse |
|---|---|---|
| Unique | Isolated(inner) | Isolated |
| Shared | Atomic(inner) | Shared |
| Weak | Weak(inner) | Shared |
| Borrow | Reference(inner, false) | Shared |
| BorrowMut | Reference(inner, true) | Exclusive |
| RawConst | Pointer(inner, false) | Shared |
| RawMut | Pointer(inner, true) | Exclusive |
| Handle | No corresponding owner variant | Unresolved policy; no invented named encoding |

Output continues to ignore ConcreteType pointer capability and derives it from
kind on reverse, as the original function documented. Handle cannot be made a
raw or borrowed pointer without changing meaning. Returning `TypeKind.Error`
or raising a precise failure is an explicit unsupported behavior change and
requires review before selection.

Reverse named generics first consult bindings, then recurse into actual type
arguments. Unknown/Infer/Error/Projection retain the prior `Named("Unknown")`
fallback. Old AST-only Constructor/Simd/Capability/DynTrait/UnitWithRepr/
SelfType/TypeBinding/ConstKeySet/DependentKeys variants are absent from the
current owner; they cannot appear in a valid input of the declared type.

`type_uses_param` recursively visits current named arguments and wrappers.
`infer_concrete_type` maps ExprKind IntLit/FloatLit/StringLit/BoolLit/NilLit,
uses the caller context for Ident, infers ArrayLit from the first element,
and preserves nil for empty arrays or unsupported expressions. Its return
annotation must be the actual `ConcreteType?`, replacing nonexistent
`has_ConcreteType?`.

## Regression oracles (not executed)

- Output Named kind retains the exact named/mangled text and empty arguments.
- Primitive aliases normalize; bindings replace a named parameter inside
  nested arrays, tuples, function signatures, and pointer wrappers.
- All seven representable pointer kinds round-trip with their declared
  capability; mutable/reference/raw distinctions are asserted separately.
- Input Union cardinality retains the documented collapse rules.
- Dict and Specialized deliberately follow their existing non-invertible
  output rules; tests must not claim exact equality for these round-trips.
- Empty/unknown expression inference returns nil; first-element arrays and
  identifier context return the expected concrete type.
- Handle has a dedicated fail-closed oracle once the policy is approved.

No build or test execution is authorized for this lane. Source review and the
parent's affected-file compile gate precede any landing or performance claims.

## Error-propagation audit: migration blocked

Root conditionally permitted Handle → TypeKind.Error only if an existing
consumer propagates/reports the error and keeps it distinct from inference.
That condition fails at the frozen base. In
`src/compiler/20.hir/hir_lowering/types.spl:1133-1135`, `lower_type` explicitly
falls through for “Infer / Atomic / Error and any unrecognized disc” and
assigns `HirTypeKind.Infer(0, 0)` without a diagnostic. The proposed Error
sentinel would therefore not fail closed. Shared → Atomic is representable
in the parser but likewise lacks downstream preservation in this consumer.

The callsite audit found no live Pure-Simple call to `concrete_to_ast_type`
outside this utility's own recursion; its module facade re-exports the API.
Rust-seed consumers cannot establish the Pure-Simple failure contract.

Consequently util.spl remains unchanged. Implementation needs explicit scope
for an actually propagated adapter failure or the HIR owner's distinct Error
handling. Do not land the mapping table above as proof of end-to-end safety.
No tests/builds were run and no candidate util migration is claimed complete.

## Source candidate after explicit Error-propagation repair

The source migration is now authorized with dependency
`f88267ea93a9f0b07b3e07188f7f0acfb26351a7` (parent-owned, independently source
reviewed). That commit gives exact parser Error its own HIR diagnostic and
HirType.Error result; legitimate Infer and other existing handling stay intact.
This dependency is not cherry-picked into this lane's tree.

The util adapter now uses Type.kind / Expr.kind and constructs real Type
wrappers with synthetic spans. Seven pointer kinds map to parser wrappers;
Handle alone emits TypeKind.Error. These are parser-boundary assertions, not
claims of downstream Atomic/Weak support. Existing HIR erasure for Atomic and Weak remains
outside this source repair.

The reverse adapter has its own independent fail-closed path: only explicit
TypeKind.Error triggers `panic("cannot monomorphize invalid AST type")`.
Generic arguments are visited before a binding replaces the base name, and a
Projection's inner type is visited before retaining its Unknown fallback, so
nested explicit Error cannot become a valid-looking named type. Legitimate
Infer and Named("Unknown") still return ConcreteType.Named("Unknown").
Panic is an established compiler invariant-failure convention, for example
`src/compiler/10.frontend/core/types.spl:1551` and
`src/compiler/10.frontend/core/flat_pool_codec.spl:471`; the authored subprocess
regressions require an actual nonzero CLI exit and the exact panic text. That
CLI behavior remains unexecuted in this lane and is not claimed verified.

Authored evidence under `test/01_unit/compiler/mono/monomorphize/`:
- parser_type_adapter_spec.spl: seven exact pointer-wrapper mappings and
  round-trips, capability derivation, explicit Handle Error, nested Optional /
  Tuple / Function / Array, names and specialization collapse, binding
  substitution, union cardinality, dictionary generic encoding, parameter
  search, literal/identifier/array inference, unknown-expression nil.
- parser_type_adapter_error_spec.spl and fixtures/parser_type_adapter/*.spl:
  direct, Optional, bound-generic, and Projection Error rejection; checks both
  process failure and exact error text so unrelated compilation failure cannot
  pass the regression.

No compiler/native/test command has been executed. Independent source review
and the parent-owned affected-file manual compile remain admission gates.

All rewritten array accumulators explicitly rebind push results for the native
value-semantics convention. Pointer/reference owner extractors receive an Error
fallback instead of the outer type itself; malformed payload fallback therefore
cannot recursively revisit the same outer node. Valid-node mappings are unchanged.

### Nested Error propagation and independent source review

A converted Error is lifted to the top-level result before constructing each
materialized Array, Tuple, Dict, Function, Optional, Pointer, or Union. Each
child is converted once and tested once; no repeated subtree validation is
introduced. This includes Shared(Handle) and Weak(Handle), whose wrapper
payloads current HIR otherwise ignores. The spec asserts Error for all 15
materialized child positions and preserves seven valid pointer controls.
Specialized(name, args) deliberately retains its preexisting authoritative
already-mangled name behavior: args are not materialized or validated, even
if they contain Handle. A separate test makes this exception explicit.

Independent source reviewer `mono_adapter_review` completed two bounded
passes. First-pass concerns (Array/Function payload extraction across colliding
enum owners and absent Named generic substitution test) were resolved by using
existing parser-owner accessors and adding a List<T> substitution oracle.
Second pass found no remaining correctness/API blocker in the source delta,
including nested Error propagation. This is source review only, not compile,
test, HIR integration, or downstream Atomic/Weak approval. All executable
regressions remain unexecuted for the parent to admit with the pinned compiler.
