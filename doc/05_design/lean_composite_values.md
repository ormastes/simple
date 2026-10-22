# Exact pure composite MIR values

This C2/C5 increment extends the existing typed/liveness exporter, not the language grammar or native runtime. It depends on the reviewed nominal declarations, recursive type graph, terminal branches and NB10 diamond implementation in PR4018/4021. It does not complete the full formal scope.

## Ownership and representations

`lean_nominal_body.spl` remains the sole changed production owner. Existing `lean_context_type_to_lean` owns type meaning and `translate_const_value_exact` owns primitive constant meaning. Array(element,size) maps to Vector(element,size); AggregateKind.Array carries the element type, as the real MIR producer records. MirConstValue.Array/Tuple provide ordered constants. Tuple[] is Unit, singleton Tuple is its sole type, and multiple elements are right-associated products. No type mapper is changed.

Array emission uses `Vector.mk` with an explicitly element-typed array literal and `by rfl`. Lean4.30 Vector has `toArray` and `size_toArray` fields; its singleton implementation uses the same literal/rfl construction. Exact count validation precedes emission. This is source-backed syntax/representation evidence; actual Lean checking remains UNRUN. Empty literals retain their element type. Tuple projection consumes the base once and emits the corresponding ordered Prod.snd chain plus Prod.fst for nonfinal positions; singleton projection is identity and empty projection refuses.

## Validation and state

The emitter validates destination/element/component types using canonical MIR type equality, preserving signedness even when Lean widths match. Constants recurse under retained component types. Primitive leaves reuse existing exact semantics, including fixed-width integer Zero; unknown FloatLexeme explicitly refuses in this owner. Struct/Enum constant representations remain unsupported, while actual Struct/Enum local values can be constructed into composites. No dictionary, boxed-value or pointer representation is inferred.

Constant recursion is bounded at128 levels including root depth1 and65536 nodes including container roots and scalar leaves. Debit each node before work, and reject an immediate child count larger than remaining nodes before allocating its term vector. This constant-node policy is separate from inherited type-mapper recursion/resource constraints and is not a global compiler memory guarantee.

Forked branch state uses independent assigned/live dictionaries and a copied scalar budget. Complete the then arm first; initialize the else scalar counter from then's remainder while forking its maps from the common prebranch state. The common suffix uses else's remainder. Both arms count even for literal conditions because both are compiled, but emitted code evaluates only the selected arm. Existing assignment union/liveness intersection is preserved. No global registry, mutation of input MIR, or cache is added.

## Route compatibility

Preserve prior nominal detection first. Composite retained type evidence selects the typed owner for call-free bodies, including instruction-free returns. Call-only composite wrappers retain the existing flat path. Actual composite operations/constants override that fallback, including Const operands in Calls and Ret/If/Switch/CallTerminator plus scalar operators; a mixed composite operation+Call refuses because this fragment adds no typed call semantics. Unsupported instruction families already refuse in the flat translator and gain no success bypass. Actual legacy output controls retain direct call and typed Result<Array> constructor expressions.

## Costs and evidence limits

Construction and constant traversal cost is proportional to actual elements/value nodes and emitted bytes. Tuple projection costs O(index); no whole-module rescans or path enumeration are introduced. Branch-state copying remains O(locals). Runtime string-copy costs, allocation failure, alias safety, max RSS and Lean/native execution remain unqualified.

The paired actual API suites and their manuals are authored UNRUN. C1 woven provenance, C2 unions/recursive Vector/general elimination, C3 unsupported contracts, C4 loops/invariants/general CFG, C5 heap/alias/cancellation/checked indexing, C6 authenticated trust choice, and C7 full transformation/native refinement remain OPEN. Existing DCE and raw ABI source packets are separate coded prerequisites, not missing features.
