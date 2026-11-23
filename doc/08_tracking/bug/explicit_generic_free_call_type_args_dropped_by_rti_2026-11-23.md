# Explicit generic free-call arguments lost by the RTI consumer

Status: source repair authored; executing validation pending a fresh producer.
No indexed claim was fabricated. The earlier claim command for the distinct
generic-method prescan bug stalled and was interrupted without claiming it.

The production regression is
`test/fixtures/compiler/generic_store_factory_result_owner/actual_attribute_store.spl`:
an imported `attr_store_detached_v1<text>` factory returns
`Result<AttributeStoreV1<text>, text>`, its `Ok` payload becomes a mutable alias,
and an unannotated match consumes `store.get(3)` after `store.set`.
Run 45159597917/job 137641255789 rejected this fourteen-production-module
projection with the retained Result ownership guard using the verified fresh
P1 executable from run 45145173990. This is not a consumer annotation defect.
The local generic-factory toy controls passed; local declaration prescans can
mask an imported RTI ownership gap. Those controls are generic factories too.

The original full P2 cache from run 45128297579 retains the failed nodes HIR:
`build/verify/p2-sharded-attempt-45128297579/diagnostics/cache/phase2/default/hir/be49e654557063cd108634a9c56805fa3be13a14ad3dda8d8d666d6fe72ebb2a.parser-v4.hir`.
Its explicit factory argument is `Str` (wire lines 134128–134138); the call has
no expression annotation (134139). The `Ok` binder raw1009 and mutable alias
raw1010 both retain `Named(owner132, [Str])` before MIR. Their wire locations
are 134184–134209 and 64333–64363 respectively. The later get call is untyped
but resolves method raw144 on owner132.

Both MIR's `enum_match_expr_type` and RTI's `callee_return` discarded the
`Call.type_args` field. RTI therefore answered with an unsubstituted factory
return, while MIR's value-argument fallback could not infer the factory's T
from its `text` and placement arguments. This can replace concrete pattern
metadata with `AttributeStoreV1<T>`, leaving the get result without complete
ownership. Actual MIR locals are not serialized in the retained cache; their
runtime values and the repaired native result remain unverified.

The repair passes explicit free-call arguments through the canonical RTI
lookup. It substitutes the exact provider row's declaration-ordered Param
indices using the existing recursive substitution, including unused binders.
It never guesses order from return occurrences or infers over explicit args.
Explicit arity mismatch and unowned nominal metadata reject. Every explicit
argument is recursively validated before checking for caller parameters;
Error/Infer and missing owners remain fatal even after a caller T. An enclosing
erased consumer's T is permitted only from independently supplied declaration
binders. MIR scopes these from the active callable and its exact qualified
method owner, saving/restoring them across nested lowering. The validated
entry retains caller Params for the existing `require_concrete` fallback;
there is no error-code remapping. The MIR ownership guard remains
unchanged, with bounded opt-in diagnostics for any remaining failure.

Nine focused cases cover imported return-only binders, nested nominal
Result ownership with out-of-occurrence declaration order and an unused
binder, explicit arity rejection, unowned argument/conflicting provider
rejection, erased consumer arguments, mixed parameter/missing-owner metadata,
mixed parameter/Error/Infer metadata, and real MIR lowering for generic free
and method-owner callers with context restoration. These cases are authored, not run.
The production fixture remains the actual native regression gate.
