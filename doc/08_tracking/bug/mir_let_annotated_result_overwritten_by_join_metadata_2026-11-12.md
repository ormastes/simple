# MIR: let-annotated Result type overwritten by untyped join metadata (2026-11-12)

Status: fix-implemented-verification-pending (MIR-lowering spec green 2026-11-13; runtime value and self-host unverified). Severity P3.

## Symptom
`val r: Result<i64, text> = if/match ... Ok(x_u8) ...`. The MIR local's HIR type metadata becomes
`Result<u8, text>` instead of the declared `Result<i64, text>`.

## Cause
At `src/compiler/50.mir/mir_lowering_stmts.spl:1799-1808`, `let_declared_type_override_v1` returns 0 for a
Result initializer, so `copy_local_hir_type_metadata` writes the untyped-join type over the annotation.

## Reachable value path
`enum_match_expr_type` (`_MirLoweringExpr/switch_operators_calls.spl:2630`, Var arm reads
`find_local_hir_type`) -> `result_ok_hir_type` (`_MirLoweringExpr/method_calls_literals.spl:544`) ->
`lower_result_unwrap_core`, which sets `result_type = self.lower_type(payload_type)` (around :1054/:1070).
So `r.unwrap()` gets MIR type U8, not I64.

## Why no wrong value has been seen yet
The witnessed values fit in 8 bits, and `mir_narrow_unsigned_integer_common_type`
(`_MirLoweringExpr/expr_dispatch.spl:200-227`) widens narrow-unsigned arithmetic to i64. A consumer that
honours U8 width directly could truncate: a u8 array store (`mir_lowering_stmts.spl:926-942`), or passing
`r.unwrap()` as a call argument.

## Origin
Found in the Fable review of PR #8499. The issue predates it; #8486 and #8499 did not widen it.

## Suggested fix
`let_declared_type_override` should prefer the declared annotation for Result initializers.

## Suggested repro
`val r: Result<i64, text> = if c: Ok(x_u8 + 0u8) else: Err("e")`, then store `r.unwrap() + 300` into an
i64 array, or pass it to `fn f(v: i64)`, and print it. Expected 300+x; a U8-honouring consumer would truncate.

## Fix (2026-11-13)
`let_declared_type_override_v1` (`src/compiler/50.mir/mir_lowering_stmts.spl`) now returns `4` when the
annotation is a settled `Result<T, E>` (no Infer, Error or `any` payload) and the initializer local
carries a `Result` HIR type. The early-Let call site then copies the initializer's metadata as before
(optional / Result-err owners, `exists_collection_locals`, isolation and resource state) and re-records
the declared type over it, so only the type changes. An `any` payload keeps the old behaviour (the
initializer wins), so nothing widens `any`.

Optional was NOT changed. Every Optional shape tried was already declared before the fix:
`val o: i64? = if c: mko(x) else: nil`, `if c: mko(x) else: mko(x)`, the same as a `match`, and the
no-join `val o: i64? = mko(x)` (with `fn mko(x: u8) -> u8?`).

## Evidence
Spec: `test/01_unit/compiler/mir/let_annotated_result_join_type_spec.spl`. The harness goes parse ->
HIR -> MIR (`MirLowering.new_for_target`) and reads the per-local HIR metadata of `pick`'s unnamed
temporaries. It was run with the Rust seed (`simple-seed-v4`, sha256 prefix `af717f53d6bce3e5`; no
`bin/simple` was deployed on the host) under `MemoryMax=16G`.

- Red before the fix: 5 of 8 examples fail. These are `val`/`var r: Result<i64, text> = if|match c:
  mk(x) | Err("e")`, the no-join `val r: Result<i64, text> = mk(x)`, and the join inside a `for` body,
  all with `fn mk(x: u8) -> Result<u8, text>`. In each, no temporary carries `Result<i64, text>`, and the
  `r.unwrap()` temporary is HIR `u8` / MIR `U8`.
- Green after: 8 of 8.
- The filed literal repro (untyped `Ok(x + 0u8)` arm) was NOT red on this base. Under an annotation the
  all-untyped-constructor join is withheld, so the binding already kept `Result<i64, text>` and the unwrap
  was I64. The overwrite needs an initializer that carries a typed `Result<u8, text>`: a typed-call join
  arm, or a direct call. The spec pins the literal repro and the Optional/nil join as green.
- Negative control: an unannotated `val r = if c: mk(x) else: Err("e")` still adopts `Result<u8, text>`
  and unwraps as U8.
- Neighbour MIR specs (18 files under `test/01_unit/compiler/mir/`, chosen for Let/Result/Optional
  lowering, out of 384): 79/93 pass both before and after, with the same 14 pre-existing failing examples
  in 9 files. That run predates the `any`-payload guard, which only narrows the fix back to the old
  behaviour.

## Unverified
- No runtime value was checked. A `Result<u8, text>` payload from `mk` is now unwrapped as I64; the spec
  checks only MIR types.
- The harness does not run the type checker. Whether the real driver accepts a `Result<u8, text>`
  initializer for a `Result<i64, text>` let is unchecked.
- Self-host and bootstrap behaviour is unchecked. Every annotated Result let in the compiler whose
  initializer is a Result now takes this path, and no bootstrap was run.
- The ordinary Let arm (`copy_local_hir_type_metadata` at ~:2144) has no override. Every shape tried,
  including `var` and a let in a `for` body, went through the early-Let path.
