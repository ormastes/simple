# RTI chained generic-factory receivers require a concrete owner

Status: open, static source diagnosis; no executing reproduction claimed.
This is separate from the repaired explicit generic free-call argument loss.
Indexed generic method return prescan and Future static-factory issues were
consulted; neither describes this exact RTI receiver boundary. No indexed
claim was created or a stalled claim command retried.

A candidate reproduction is an erased generic caller using
`factory<T>().get()` when the factory declares `Store<T>` and the store's
method return depends on T. A concrete `factory<text>().get()` is a distinct
control; a local `store` variable is the production fourteen-module fixture's
shape and does not traverse this chained receiver path.

In `src/compiler/20.hir/return_type_interface_v1.spl`,
`receiver_owner_with_args` first accepts an independently declared receiver
type. Without one, its chained-expression fallback calls
`callee_return(receiver, symbols, None)` and immediately invokes
`resolve`/`require_concrete`. It does not carry the active caller's declaration
binders into that nested call. Even before explicit argument handling, a
generic factory return containing a provider Param failed this concrete
requirement with E-RTI-003. That error propagated through `method_return` to
MIR's outer fatal error branch. Consequently this shape was already rejected;
the free-call repair does not establish support for it.

Passing caller binders alone cannot repair the boundary: the legitimate
`Store<T>` receiver still contains caller Params and is not concrete. A future
owner repair must preserve the independently proven nominal Store identity,
carry caller binders through nested calls, and substitute method results in
that scoped symbolic context. It must reject unrelated/unbound parameters and
missing nominal owners. Broadly treating outer E-RTI-003 errors as successful
lookup would hide other ownership errors and is not an acceptable repair.

Required regression evidence: a real parsed imported factory and generic
owner method, positive concrete and erased-generic chains, negative unbound
caller parameters and missing owners, nested parameter containers, and exact
native output with the verified producer. No workaround, guard change, or
runtime PASS is supplied by this report.
