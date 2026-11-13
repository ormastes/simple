# MIR: let-annotated Result type overwritten by untyped join metadata (2026-11-12)

Status: FIXED (MIR-lowering spec evidence, 2026-11-13; self-host verification pending). Severity P3.

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
annotation is a settled `Result<T, E>` (no Infer/Error payload) and the initializer local carries a
`Result` HIR type. The early-Let call site then copies the initializer's metadata as before (optional /
Result-err owners, `exists_collection_locals`, isolation and resource state) and re-records the declared
type over it, so only the type changes. Optional was not changed: no red case could be built (see below).

## Evidence
Spec: `test/01_unit/compiler/mir/let_annotated_result_join_type_spec.spl` (parse -> HIR -> MIR via
`MirLowering.new_for_target`, reads per-local HIR metadata of `pick`'s unnamed temporaries), run with the
Rust seed (`simple-seed-v4`, sha256 prefix `af717f53d6bce3e5`) under `MemoryMax=16G`.

- Red before the fix: 3 of 6 fail. `val`/`var r: Result<i64, text> = if|match c: mk(x) | Err("e")` with
  `fn mk(x: u8) -> Result<u8, text>`: no temporary carries `Result<i64, text>`, and the `r.unwrap()`
  temporary is HIR `u8` / MIR `U8`.
- Green after: 6 of 6.
- The literal repro above (untyped `Ok(x + 0u8)` arm) was NOT red on this base. Under an annotation the
  all-untyped-constructor join is withheld, so the binding already kept `Result<i64, text>` and the unwrap
  was I64. Only a typed-call arm (`remember_merged_result_ctor_arm_type` / all-typed join) reached the
  overwrite. The spec pins the literal repro as green.
- Optional `val o: i64? = if c: mko(x) else: nil` (with `mko -> u8?`) was already declared before the fix.
  It is pinned green.
- Negative control: an unannotated `val r = if c: mk(x) else: Err("e")` still adopts `Result<u8, text>`
  and unwraps as U8.
- Neighbour MIR specs (18 files under `test/01_unit/compiler/mir/`, chosen for Let/Result/Optional
  lowering): 79/93 pass both before and after, with the same 14 pre-existing failing examples in 9 files.

## Unverified
No runtime value was checked. A `Result<u8, text>` payload from `mk` is now unwrapped as I64; the spec
checks only MIR types. Self-host and bootstrap behaviour is also unchecked: every annotated Result let in
the compiler whose initializer is a Result now takes this path, and no bootstrap was run. The second Let
site (`mir_lowering_stmts.spl` ordinary Let arm, near `copy_local_hir_type_metadata` at ~:2144) has no
override. The `var` case is fixed through the early-Let path, but that site was not shown to be reachable
or unreachable for this shape.
