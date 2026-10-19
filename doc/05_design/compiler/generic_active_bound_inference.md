# Active HM direct-function bound admission

Status: source candidate; runtime, compiler, and SSpec execution UNRUN. This is a prerequisite slice of the full generic hardening plan, not full P1/G2/G3/G7 closure.

## Existing path and causal defects

`hir_typecheck_consumer_v1` constructs `HmInferContext.with_builtins` and calls `infer_module`. The module entrypoint previously never collected trait declarations/implementations/function bounds or solved obligations. Generic signatures use `Named(SymbolId)` binders while HM scheme instantiation substitutes only `Infer` variables. Explicit call arguments therefore did not instantiate the signature; inferred arguments never reached bound generation; NamedVar was omitted. The old HIR-to-solver adapters also assigned SymbolId values into HirSymbol fields and dropped associated metadata.

## Owner-local implementation

`infer_module` first snapshots declaration metadata and creates the existing TraitSolver with the same module symbol table, then registers traits and impls before any function body. `trait_collection` resolves real trait and binder rows; retained method and associated-type metadata pass through their existing solver types. Inherent impls do not create sentinel traits. Trait declaration where clauses and parameterized bound forms receive precise unsupported diagnostics rather than erasure.

Both direct HIR variable forms carry SymbolId. `generic_calls` uses that identity to find body-free declared signatures in the existing FunctionBoundContext. It creates ordinary HM fresh variables in declaration order, constrains the explicit prefix, and extends the existing instantiation walker to replace declared Named/TypeParam binders, including composite/effect carriers. Existing inference checks each value argument and the result. Only successful direct calls retain their binder variables and caller identity.

After all bodies and expected-result constraints, declared defaults constrain still-unresolved arguments. A separate pass resolves all pending bound arguments. Exact matching caller bounds discharge rigid generic forwarding obligations; unresolved or foreign nominal arguments cannot masquerade as concrete evidence. Concrete Named types require actual Struct/Class/Enum rows recursively. The existing solver receives actual symbols, types, and call spans. All solver error variants enter HM diagnostics. The independently reviewed conditional-solver prerequisite completes child obligations synchronously, detects recurrence, and preserves ambiguity.

Function environments restore after each body and both function/parameter symbols have raw-ID bindings, preserving Var/NamedVar identity and preventing parameter leakage between functions. No heuristic method obligations are promoted into direct-function admission: that preexisting queue is retained separately pending resolved method-owner integration.

## Boundaries and next required work

The current flat bridge drops function and impl binder bounds/defaults. Tests attach bounds/defaults to actual parsed HIR binders; they do not manually install solver declarations. Source syntax admission remains OPEN. Next owner work is the existing AST/Core declaration bound transport through `_FlatAstBridge/convert_nodes` and `module_assembly`, then source-only positive/negative infer_module scenarios without injected bounds.

Full method/static/indirect-function bound propagation, richer generic forwarding proofs, parameterized traits, associated-type normalization, generic trait where clauses, cross-module/imported symbol authority, complete default semantics, declaration conformance, and compiler publication severity remain OPEN. The driver policy is unchanged: Critical/Deny, Robust/Warn, and advisory tiers are separate from this HM error collection. No mono-to-HM sibling-private dependency is introduced.

## Cost and evidence

Work occurs only on the existing HM entrypoint. Metadata retains one body-free signature per function, not whole function bodies. Pending calls are bounded by encountered direct calls and cleared after the module. There is no persistent cache or new scan of files, process launch, or startup hook. Extra signature/type walks are linear in traversed type trees; aggregate performance and native memory behavior remain unmeasured.

Acceptance is the actual infer_module SSpec and the separately pinned public solver suite. Authored scenarios are not runtime evidence. Independent review is required before root composition; root owns all execution and end-to-end admission.

## Revision 2 authority correction

Independent finding ACTIVE-HM-001 identified that an exact symbolic ID match bypassed concrete-path symbol validation. Collection now validates function/method rows, unique ordered binder IDs/names, TypeParam/Trait kinds, row identity, and explicit module ownership before atomically publishing any metadata. The same bound-symbol resolver is reused by concrete generation. Failed collection publishes neither bounds nor assumptions. Four additional actual infer_module negatives cover missing trait row, wrong trait kind, foreign binder owner, and wrong function kind; the valid forwarding control remains.

The existing Substitution.apply walker does not yet recurse through Throws, Union, or Isolated. Extending declaration instantiation does not establish full substitution/admission support for those forms. Composite/effect qualification remains OPEN; no broad pass is claimed.
