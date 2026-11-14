# MIR mutable-reference roots and public forwarding audit

Source audit found two independent causes of the transient-boundary gate failure.

`MirBuilder.mut_ref_param_ptrs` and `mut_ref_param_values` are allocated/reset in `begin_function`, populated during mutable-reference parameter lowering, and consumed by `set_terminator` to write values back before return. The retained builder's promotion inventory omitted both child arrays. Add each as an explicit root: promoting the older parent alone is not the inventory's lifetime contract. No native use-after-free was demonstrated; the next begin_function resets these arrays, so this report does not assert an observed ordinary-path dangling read.

The SFFI forwarding helper is public, but the shell scanner only recognized `fn` and therefore extracted no body for `pub fn`. Recognize optional public visibility at start/end boundaries while retaining exact promote/free/return body comparison. Positive public declarations and a following public helper must pass; deleting the release from a public helper must fail.

Evidence: one run of `sh scripts/check/check-mir-transient-scope-boundary.shs` passed its unconditional 35 mutation fixtures and all 18 production source invariants. The existing Simple ownership spec now also enumerates every MirBuilder child, including both writeback arrays. Simple specs, native lifetime tests and bootstrap were UNEXECUTED under the user's bugfix verification waiver. Static assurance does not establish native lifetime correctness or Phase 3 qualification.
