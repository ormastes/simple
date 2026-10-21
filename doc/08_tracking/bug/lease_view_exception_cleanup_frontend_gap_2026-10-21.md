# Lease view cleanup has no admitted source exception-unwind route

Status: OPEN; source inspection only, no new runtime qualification.

The scalar lease adapter invalidates its epoch after a synchronous callback
returns. `lease_with_view_result` additionally invalidates before propagating
`Err`, including a callback that returns early with postfix `?`. These are
normal language return paths. They do not establish panic/exception unwind
cleanup, and AC-BOR04 compiler static enforcement remains incomplete.

## Concrete gap

The pure-Simple flat frontend only constructs postfix `ExprKind.Try` at
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (EXPR_TRY arm).
Its core AST/parser and bridge have no source construction path for
`ExprKind.TryCatch`; the parser-type enum and generated visitors alone do not
make try/catch/finally source syntax available. HIR/MIR contain TryCatch and
finally cleanup lowering, but that is not evidence for this source route.

The native bridge's defer implementation explicitly documents its narrower
scope at `convert_nodes.spl:1692`: top-level deferred statements are replayed
before explicit returns and fallthrough. Nested defer and errdefer placements
fail closed. This mechanism does not protect a caller's active lease-view epoch
when a callee unwinds rather than returning.

## Required repair and acceptance

Admit an actual source-to-native recoverable exception/cleanup route before
claiming unwind-safe callback views. Prove a callback saves its view, throws,
and an outer handler observes that saved view as invalid; prove a subsequent
fresh callback works. Cover nested cleanup, rethrow, and every supported
backend. Unsupported backends must reject the construct explicitly. See also
[the backend unwind ABI tracking](recoverable_unwind_backend_abi_missing_2026-08-25.md).

Until then, callers needing recoverable callback errors must use
`lease_with_view_result`. The compatibility void callback API requires normal
synchronous completion; unrecoverable panic/exception unwinding is unsupported.
