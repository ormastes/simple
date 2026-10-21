# Contextual new: locally proven scope repair

**Status: SOURCE PATCH ONLY; PARTIAL HOLD; all production execution UNRUN.**

The actual parser, flat bridge, HIR function scopes and MIR serializer are the test counterparts. The spec compares distinct contextual and ordinary identifier ASTs; it does not model parser behavior.

| Scenario | Observable acceptance |
|---|---|
| Original bound `new[index]` | Canonical Index receiver retains parameter SymbolId |
| Multiplication, unary minus, grouped counterpart | Same actual AST structure as ordinary `items[index]`; no greedy allocation capture |
| Scalar local initializer `val new = new[37]` | Initializer remains allocation; following index resolves the new local |
| Nested block shadow | Inner index resolves inner Let SymbolId; outer tail restores parameter SymbolId |
| Function/block exit and malformed-source reset | Later unbound `new[1]` remains allocation |
| Explicit `new() [1]` under bound `new` | Existing allocation remains allocation |
| Supported `(new) => new[0]` | Existing arrow parameter body parses as canonical Index |
| Real MIR lowering | Exactly one rt_array_get for original bound array read, no HIR/MIR errors |
| Native exact-spelling fixture | Exit 0 only for arithmetic 17/-4/20, local 37, allocation payload 41 |

Tests are authored, not executed. Source inspection predicts old-parser failures for the indexed and precedence cases. No executed RED/PASS or producer qualification is claimed.

The `contextual_new_unknown_import` fixture is deliberately an **expected miss/HOLD**, not a passing full-feature proof: imported alias `new` lacks actual production imported-surface authority at parser time. Its complete acceptance is imported payload 23; this partial repair is expected still to misparse it. `shadow.spl` exposes a nearer opaque import so an outer parameter cannot silently supply false Value evidence.

Other unresolved cases: module forward/type/import authority, method keyword parameters, unmodeled match/comprehension binders, tuple declaration within-RHS/per-element visibility and tuple-loop positive admission. These do not receive invented absence semantics. This packet cannot close the full bug or retire the six workaround consumers.

Final cycle3 adds actual parser assertions for initialized/no-init var, scalar for iterable/body/exit, custom fn/backslash lambda block restoration, captured values through fn/backslash/pipe/zero-arrow lambdas, multi-arrow parameters, and opaque import bound-before/unknown-inside/bound-after. The original facet member spelling has a direct Field(Index(...), stable_entity_id) assertion. The context query uses a `me` receiver so it borrows the owner rather than copying its scope stack. No benchmark or runtime execution is claimed.
