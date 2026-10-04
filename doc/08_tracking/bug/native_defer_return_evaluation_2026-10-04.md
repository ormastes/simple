# Native defer must preserve return evaluation order

Status: repair drafted; rebuilt-compiler validation pending.

The flat AST bridge previously inserted pending cleanup statements before
an explicit return expression was evaluated. It also rejected typed implicit
tails with `__defer_unsupported_placement__`. The latter blocks the HIR codec
and codec-support modules during the Windows Phase 3 bootstrap.

A reduced native build with LLVM producer SHA-256
`84c36744623a49a91f1bb108ad987431719ea5a61969ea42ed5f1e18993b5ff3`
reproduced that rejection with a typed implicit tail. This is a compiler
limitation, not evidence that the cleanup can be discarded.

The repair evaluates the return expression into a bridge-owned local before
replaying cleanup groups in reverse registration order, retaining statement
order within each group. It then returns the saved value. A `$` in the local
name makes it unavailable to source identifiers; the raw statement ID
distinguishes generated bindings. Explicit returns without pending cleanup
keep their existing lowering. Nested defer and errdefer remain refused.

`test/fixtures/compiler/native_defer_return_order.spl` must compile and exit
zero, printing integers 1 through 15 in order, one per line. It covers
explicit and implicit returns, LIFO order, early conditional returns, unit
fallthrough, text and array payloads, and block cleanup. The separate
`native_defer_nested_refused.spl` fixture must fail with the existing
unsupported-placement diagnostic.

These checks have not yet run with the repaired compiler. The separate
array/import repair build uses frozen source and does not contain this patch.
