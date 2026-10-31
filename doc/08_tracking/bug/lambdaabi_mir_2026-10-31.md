# lambdaabi MIR failures (stage3 self-host), 2026-10-31

## Root bugs
1. `lib.nogc_async_mut.io.buffer`: `fut.then(\result: match ...)` -- the lambda's declared function slot
   `fn(T) -> Future<U>` of the generic `Future.then<U>` keeps unresolved type params/Infer, so
   `lambda_abi_type_resolved` (src/compiler/50.mir/_MirLoweringExpr/lambda_abi.spl) fails and
   switch_operators_calls.spl:7674 raises "lambda function slot has an unresolved ABI type".
   Typed receivers and explicit `then<R>` do not help (repro: pinned stage2, 14 errors in module).
2. `compiler.hir.hir_lowering.statements`: `init ?? Expr(kind: ExprKind.NilLit, ...)` trips
   expr_dispatch.spl:6402 "null coalesce fallback does not match declared record owner".

## Workaround sites
- src/lib/nogc_async_mut/io/buffer.spl:154
- src/lib/nogc_async_mut/io/buffer.spl:185
- src/lib/nogc_async_mut/io/buffer.spl:202
- src/lib/nogc_async_mut/io/buffer.spl:335
- src/lib/nogc_async_mut/io/buffer.spl:354
- src/lib/nogc_async_mut/io/buffer.spl:371
- src/lib/nogc_async_mut/io/buffer.spl:396
- src/lib/nogc_async_mut/io/buffer.spl:413
- src/compiler/20.hir/hir_lowering/statements.spl:811

Buffer: each `.then` lambda replaced by an inline `poll()` match (Ready -> same body with explicit return,
Pending -> `Future.pending<R>()`), identical to Future.then semantics. statements.spl: `if val init_expr = init`
instead of `init.? ... init ?? fallback`.

## Removal condition
Remove once the root fix (generic lambda slot ABI resolution / record-owner check for aliased record) is in a stage2 used for bootstrapping.
