---
id: cuda_backend_mirop_signature_field_semantic_false_positive_2026-07-29
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).
severity: medium
discovered: 2026-07-29
fixed: 2026-07-30
discovered_by: lane CUDA1 (cuda-symbolid-layout) while running test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl
fixed_by: lane SIGF (mirop-signature-false-positive)
related: test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl
related: src/compiler/70.backend/backend/cuda_backend.spl
---

# `emits direct device calls by symbol name` fails with a false `MirOperand has no field named signature` semantic error

## Symptom

Running `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`
(the CUDA backend intensive MIR contract suite) always fails one example:

```
✗ emits direct device calls by symbol name
    semantic: class `MirOperand` has no field named `signature`
```

The other 9 examples in the same file pass, including two new ones added by
lane CUDA1 that exercise a completely unrelated code path (Struct(SymbolId)
field-layout resolution). This failure is **pre-existing** and unrelated to
the CUDA1 change: it reproduces identically before and after CUDA1's edits to
`cuda_backend.spl` (confirmed by re-running after reverting a keyword-naming
mistake CUDA1 introduced and fixed separately — the failure persisted
unchanged).

## Suspected cause

The failing test (`test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl:79-97`)
builds a direct-call `MirOperand` via
`MirOperand(kind: MirOperandKind.Const(MirConstValue.Str("cuda_add"), MirType(kind: MirTypeKind.FuncPtr(callee_signature))))`
and a `MirInstKind.Call(...)` instruction. Neither `MirOperand` nor any of its
variants declare a field literally named `signature` — `cuda_backend.spl`'s
own `func.signature` accesses are on `MirFunction`, not `MirOperand`. This
looks like a false positive from whatever static/semantic checker runs ahead
of test execution (test-runner "semantic:" pre-check, not a runtime
assertion failure) — plausibly confused by the `FuncPtr(signature: MirSignature)`
payload name inside `MirTypeKind` while resolving a field access chain
through `Const(_, ty)` -> `ty.kind` -> `FuncPtr(signature)`, and misattributing
the payload binding name `signature` as a field expected on `MirOperand`
itself.

## Scope note

Not fixed as part of lane CUDA1 (cuda-symbolid-layout): the failure is in the
`compile_direct_call`/semantic-check path, which CUDA1 did not touch (CUDA1's
changes were confined to `field_layout`, `compile_aggregate`, `compile_gep`,
and the new `cuda_can_size`/`cuda_type_size`/`cuda_type_align` family). Root
cause needs someone with context on the test-runner's static "semantic:"
pre-check (likely in the compiler's semantic-analysis pass, not
`cuda_backend.spl`).

## Root cause (found by lane SIGF, 2026-07-30)

The "semantic:" prefix is misleading — this is not a static/pre-check false
positive at all, it is a **runtime interpreter variable-shadowing bug**, and
`cuda_backend.spl` genuinely triggers it (classification: **(a) real product
bug reachable only when this example runs**, not a checker artifact).

`compile_instruction(builder: PtxBuilder, inst: MirInst, func: MirFunction)`
in `src/compiler/70.backend/backend/cuda_backend.spl` (was line 375) matched
`inst.kind` and, for the `Call` variant, bound the callee payload with the
same name as the method's own `func: MirFunction` parameter:

```
case Call(dest, func, args):
    val call_result = self.compile_call(builder, dest, func, args)
```

`MirInstKind.Call` is declared `Call(dest: LocalId?, func: MirOperand, args:
[MirOperand])` (`src/compiler/50.mir/mir_instruction_kinds.spl:51`) — so the
match-arm payload name `func` is literally a `MirOperand`, colliding in name
with the enclosing method's `func: MirFunction` parameter. The seed
tree-walk interpreter (the engine `bin/simple test` runs on) does not give
this match arm its own scope for the purpose of the caller's binding: after
`compile_instruction` returns, `compile_function`'s own `func` local (up in
its own stack frame, used again at
`func.signature.return_type` for the terminator step, `cuda_backend.spl:225`)
had been silently overwritten by the arm's `func` (the `MirOperand` callee)
whenever the block being compiled contained a `Call` instruction. The next
read of `func.signature` therefore dereferenced `.signature` on a
`MirOperand` value instead of the intended `MirFunction`, producing exactly
`class \`MirOperand\` has no field named \`signature\``. This is the same
family of bug already flagged in a comment a few lines above (`cuda_backend.spl`
~130: "the bootstrap interpreter currently misbinds that payload accessor"),
just recurring at the match-arm level instead of the nested-destructuring
level that comment was originally about.

Confirmed by minimal repro (`CudaBackend.create(...).compile(...)` on the
exact MIR from the failing example) and by the fix below turning the example
green with no other behavior change.

### Fix

Renamed the match-arm payload from `func` to `callee` (matching
`compile_call`'s own parameter name) so it no longer collides with
`compile_instruction`'s `func: MirFunction` parameter:

```
case Call(dest, callee, args):
    val call_result = self.compile_call(builder, dest, callee, args)
```

### Two more pre-existing defects found and fixed while restoring 10/10

Getting the suite to 10/10 (not just the filed example) surfaced two more
bugs in the *first* example ("emits if branches and loop backedges..."),
both pre-existing and unrelated to the `.signature` false positive:

1. **Register-id collision in `PtxBuilder`.** `alloc_reg()` numbers
   temporaries from an internal `next_reg` counter that starts at 0 and is
   never advanced past the fixed MIR-local register ids a function actually
   uses (`reserve_reg_id()` existed in `cuda/ptx_builder.spl` for exactly
   this purpose but was never called from anywhere). A `bool`-typed kernel
   argument's predicate register (`%r0`, from the local's own id) and the
   very first builder-allocated temp (also `%r0`, since `next_reg` was still
   0) landed on the same PTX register name, corrupting the `setp.ne`
   self-comparison. Fixed by calling `builder.reserve_reg_id(local.id.id)`
   for every local at the top of `compile_function` before any temps are
   allocated.
2. **Test asserted an invalid PTX instruction.** The example asserted
   `setp.ne.u8 %r0`, but PTX's `setp` instruction has no 8-bit comparison
   form (valid widths are `.u16/.u32/.u64/.s16/.s32/.s64/.b16/.b32/.b64/.f32/
   .f64` — see PTX ISA `setp` reference); the backend correctly widens the
   `ld.param.u8`-loaded byte into a `.u16` temp before comparing, which is
   the only way to emit assemblable PTX here. Updated the assertion to
   `setp.ne.u16 %r0` to match the (already correct) hardware-legal output.

### Files changed
- `src/compiler/70.backend/backend/cuda_backend.spl` — renamed `Call` arm
  payload `func` → `callee`; added `reserve_reg_id` reservation loop in
  `compile_function`.
- `src/compiler/70.backend/backend/cuda/ptx_builder.spl` — unchanged (the
  already-present `reserve_reg_id` is now actually called).
- `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl` —
  `setp.ne.u8 %r0` → `setp.ne.u16 %r0` assertion fix, with a comment
  explaining PTX's `setp` width constraint.

### Verification
- `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`:
  `Results: 10 total, 10 passed, 0 failed`.
- `test/01_unit/compiler/semantics/param_mutability_semantic_spec.spl`:
  `Results: 4 total, 4 passed, 0 failed`.

## Repo sweep result (2026-07-30, lane SHDW1)

Repo-wide heuristic sweep of `src/compiler/**` (numbered dirs; the
`backend/driver/hir/interp/mir/types/...` top-level entries are symlinked
spellings of the same trees, so each file was edited through exactly one
spelling) for the same landmine shape: a `case Ctor(binding, ...):` payload
name that collides with a parameter of the enclosing function, or of a
caller/callee pair in the same file, such that the interpreter's match-arm
scoping leak corrupts the other function's same-named local after the arm
runs / after the call returns.

**Method:** wrote a 3-pass heuristic Python scanner (kept out of the repo, in
the session scratchpad: `scan_shadow.py` collects per-file fn/method param
lists + `case` arm bindings via indentation-scope tracking; `scan_shadow2.py`
cross-references caller/callee param-name collisions with a "reused after the
call site" token check; `scan_shadow3.py` refines same-fn hits by checking
reuse specifically after the *enclosing match statement* ends, not just after
the individual arm, to avoid false-positiving on big one-`match`-body
dispatcher functions). A bug in the scanner itself (an off-by-one in the
paren-matcher used to find a function signature's closing `)`) initially
produced wildly wrong function-scope boundaries and ~1163 mostly-noise raw
hits; fixed and re-verified against a known-good case before trusting any
further output. Final pass produced 81 deduplicated candidate collisions
across `src/compiler/**`, each manually inspected for a genuine post-call/
post-arm read of the shadowed name.

`cuda_backend.spl` was re-scanned fresh at the end of the sweep (it was
synced from origin mid-session) — zero hits in its current content, no action
needed.

### Classification table

| file:line | enclosing fn | param | arm (ctor) | class | action |
|---|---|---|---|---|---|
| `95.interp/mir_interpreter.spl:271,333,858` | `execute_function` (caller, param `func`) / `execute_instruction`, `execute_terminator` (callees) | `func` | `Call`, `PipeForward`, `CallTerminator` | (a) real, cross-fn: `execute_function` reads `func.name` in its infinite-loop-guard debug line after the instruction/terminator loop | renamed callee arm bindings `func`→`call_target`; unused `PipeForward` binding →`_func` |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl:108` | `vhdl_catalog_signature` (caller, param `signature`) / `vhdl_catalog_type` (callee) | `signature` | `FuncPtr` | (a) real: caller reads `signature.is_variadic` after the callee recurses over `signature.params` | renamed `signature`→`inner_sig` |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl:156,181` | `vhdl_catalog_function` (caller, param `func`) / `vhdl_catalog_inst`, `vhdl_catalog_terminator` (callees) | `func` | `Call`, `CallTerminator` | (a) real: caller rebuilds `MirFunction` from `func.*` fields after the per-instruction/terminator loop | renamed `func`→`callee` |
| `70.backend/backend/vhdl_entity_compile.spl:422` | `compute_inline_exprs` (caller, param `func`) / `inst_used_ids` (callee) | `func` | `Call` | (a) real: caller reads `func.locals` right after the `inst_used_ids` loop | renamed `func`→`callee` |
| `60.mir_opt/mir_opt/simd_lowering.spl:50` | `lower_function_simd` (caller, param `func`) / `lower_block_simd` (callee) | `func` | `Call` | (a) real: caller does `MirFunction(..func, ...)` spread after the per-block loop | renamed `func`→`callee` |
| `30.types/bidirectional_inferencer.spl:91`, `bidir_phase1a.spl:175`, `bidir_phase1b.spl:100`, `bidir_phase1c.spl:166`, `bidir_phase1d.spl:136`, `type_infer/inference_expr.spl:244` | `check_expr` (caller, param `expected`) / `infer_expr` (callee) | `expected` | `Check`/`InferMode.Check` | (a) real, recurring across 6 near-identical bidirectional-inference files: `check_expr` reads its own `expected` param after calling `infer_expr(..., Check(expected))` in almost every branch (`Lambda`, `Let`, `Return`, `Tuple`, `ArrayLit`, `If`) | renamed callee arm binding `expected`→`target_ty` in all 6 files |
| `30.types/type_system/bidirectional.spl:111,114` | `check_lambda` (caller, params `params`, `expected_params`, `expected_ret`) / `check_expr` (callee, nested-lambda `Lambda`/`Function` arms) | `params`, `expected_params`, `expected_ret` | `Lambda`, `Function` | (a) real for nested lambdas: a doubly-nested lambda type-check re-enters `check_expr`'s own `Lambda`/`Function` arms with the same names `check_lambda` uses after the recursive `check_expr` call returns | renamed arm bindings `params`→`lambda_params`, `body`→`lambda_body`, `expected_params`→`fn_expected_params`, `expected_ret`→`fn_expected_ret` |
| `35.semantics/const_eval.spl:249,253,259,263,267,271` | `eval_binary`/`eval_unary`/`eval_named_var`/`eval_call`/`eval_static_call`/`eval_if` (callers, params `op`,`left`,`right`,`operand`,`symbol`,`name`,`args`,`type_`,`method`,`cond`,`then_`,`else_`) / `eval` (callee, one big dispatcher over `expr.kind`) | (all of the above) | `Binary`,`Unary`,`Var`,`NamedVar`,`Call`,`StaticCall`,`If` | (a) real and wide-reaching: `eval` is recursive over itself for nested const expressions, and its dispatcher arms reuse literally every sibling `eval_*` method's own parameter names — any nested binary/unary/call const-expression recurses back into `eval`, which can corrupt whichever sibling's param is currently on the stack | renamed every arm binding in `eval`'s match with an `e_` prefix (`e_op`, `e_left`, `e_right`, `e_operand`, `e_symbol`, `e_name`, `e_callee`, `e_args`, `e_type`, `e_method`, `e_cond`, `e_then`, `e_else`) |
| `35.semantics/resolve.spl:329` (was) | `resolve_block` (caller, param `block`) / `resolve_stmt` (callee) | `block` | `Block` (stmt) | (a) real: caller reads `block.value`/`block.span` after the per-statement loop; any nested block statement (if/while/nested-block body) re-enters this arm | renamed `block`→`inner_block` |
| `35.semantics/resolve.spl:452,488` | `resolve_block` (caller, param `block`) / `resolve_expr` (callee, `If`'s `Some(block)` and `Block` arms) | `block` | `Some`, `Block` (expr) | (a) real: same mechanism — `resolve_block` reads `block.span` after calling `resolve_expr` on its trailing value expression, which can itself be an `if`/`block` expression | renamed `Some(block)`→`Some(else_block)`, `Block(block)`→`Block(inner_block)` |
| `35.semantics/resolve.spl:343,363` | `resolve_call_args` (caller, param `args`) / `resolve_expr` (callee, `MethodCall`/`Call` arms) | `args` | `MethodCall`, `Call` | (a) real and high-frequency: `resolve_call_args`'s own `while arg_idx < args.len():` loop calls `self.resolve_expr(arg.value)` per argument — any argument that is itself a call/method-call expression recurses into `resolve_expr`'s `args`-binding arm, which can corrupt the **loop's own termination condition** (`args.len()`) on the next iteration | renamed both arm bindings `args`→`call_args` |
| `20.hir/inference/unify.spl:165` | `occurs_check` (caller, param `id`) / `resolve` (callee) | `id` | `Var` | (a) real: `occurs_check` reads `id.eq(other_id)` right after `self.resolve(ty)`, and `ty` is frequently itself a `Var` | renamed `resolve`'s arm binding `id`→`var_id` |
| `70.backend/backend/common/type_mapper.spl:85,94`, `llvm_type_mapper.spl:162,168`, `cranelift_type_mapper.spl:125`, `interpreter_type_mapper.spl:115`, `wasm_type_mapper.spl:130` | `map_array`/`map_function` (callers, params `element`,`size`,`params`,`ret`) / `map_type` (callee dispatcher, same file, per-backend override) | `element`,`size`,`params`,`ret`,`fields`,`elements`,`members`,`inner`,`mutability` | `Ptr`,`Struct`,`Array`,`Tuple`,`Union`,`Function` | (a) real, recurring across 5 near-identical type-mapper files: e.g. `map_array`'s `"[{size} x {elem_ty}]"` reads `size` after `self.map_type(element)`, which corrupts it whenever `element` is itself a nested array/function type | renamed every dispatcher arm binding with a `t_` prefix in all 5 files |
| `70.backend/backend/native/isel_x86_64.spl:29`, `isel_aarch64.spl:46`, `isel_riscv32.spl:134`, `isel_riscv64.spl:127` | `isel_store`/`isel_set_field` (callers, param `value`) / `lower_operand` (callee dispatcher) | `value` | `Const` | (a) real, recurring across 4 ISA backends: e.g. `isel_store(ctx, ptr, value)` calls `lower_operand(ctx, ptr)` before reading `value` again — if `ptr` is itself `Const`, the callee's `Const(value, type_)` arm corrupts the caller's `value` param | renamed dispatcher arm bindings `value,type_`→`const_value,const_type` in all 4 files |
| `70.backend/backend/_MirToLlvm/core_codegen.spl:1402,1581` | `translate_store`/`translate_store_global` (callers, param `value`) / `translate_operand`, `get_operand_type` (callees) | `value` | `Const` | (a) real: `translate_store_global` calls `self.translate_operand(value)` then reads `value` again immediately after — if `value` itself is `Const` (the common case for a static initializer), the callee's own arm corrupts it on that very call | renamed both dispatcher arm bindings `value,type_`→`const_val,const_ty` |
| `70.backend/backend/interpreter_calls.spl:410,424` | `try_call_builtin` (own param `name`) | `name` | `Value.String` (nested, inside `BuiltinTag.EnvGet`/`EnvSet`) | (b) false positive: whole function body is one `match tag:` dispatch with no code after the match; the "reuse" the scanner found was a sibling nested-match branch, not a post-match read | left alone |
| `30.types/type_system/expr_infer.spl:246..478` (18 arms) | `infer_expr` (own param `expr`) | `expr` | `ListComprehension`,`Spawn`,`Await`,`New`,`Cast`,`Try`,`ExistsCheck`,`UnwrapOr`,`UnwrapElse`,`UnwrapOrReturn`,`Coalesce`,`OptionalChain`,`CastOr`,`CastElse`,`CastOrReturn`,`Spread`,`DictSpread`,`ContractOld` | (b) false positive: `infer_expr`'s entire body is one `match expr:` whose value is the function's return value — no trailing code observes a stale `expr` | left alone |
| `70.backend/backend/llvm_lib_translate.spl:243` | `compile_function` (own param `func`) | `func` | `CallTerminator` | (b) false positive: manually traced every read of `func` in the function — all occur before the terminator-translation block; nothing reads it after | left alone |
| `35.semantics/safety_checker.spl:447,502,548,558,585,934` | various (`block`, `args`) | — | `Block`,`Some`,`Call`,`MethodCall` | (c) excluded — file is on the do-not-touch list for this lane | not reviewed further, flagged for a future lane |
| `20.hir/hir_lowering/expressions.spl:895,928` | `lower_hir_expr` (own param `e`) | `p` (`Some`), `asm_node` (`AsmBlock`) | `EnumLit` payload, `AsmBlock` | (b) false positive: enclosing method's own param is `e`, not `p`/`asm_node`; the whole `match e.kind:` is the method's tail expression (its result feeds `HirExpr(kind: kind, ...)`), and neither arm-local binding is read after its own arm. `asm_node` textually matches `lower_asm(asm_node: AsmExpr)`'s own param, but that's the callee being invoked in the same expression, not a stale post-call read of the caller's own param (IMP2 module-call keying untouched, per instructions) | left alone |
| `30.types/const_keys_phase8b.spl:183` | `to_string` (own params: none, `self` only) | `args` (`Generic`) | `Generic` | (b) false positive: `to_string()` takes no parameters at all, and `match self:` is the entire function body (tail expression) — no trailing code anywhere reads `args`/`base` | left alone |
| `30.types/type_infer/inference_control.spl:507` | `infer_stmt` (own param `stmt`) | `block` (`Block`) | `Block` | (b) false positive: own param is `stmt`, not `block`; `case Block(block): self.infer_block(block)` is the last arm of `match stmt.kind:`, which is `infer_stmt`'s tail expression — nothing follows | left alone |
| `30.types/type_infer/inference_effects.spl:175` | `infer_stmt_effects` (own param `stmt`) | `block` (`Block`) | `Block` | (b) false positive: same shape as above — own param `stmt`, arm is the match's last/tail case, function ends there | left alone |
| `30.types/type_system/effect_pass.spl:381` | `scan_stmt` (own param `stmt`) | `block` (`Block`) | `Block` | (b) false positive: own param `stmt`; `case Block(block): scan_block(block)` is the tail arm of the function's sole `match stmt.kind:` | left alone |
| `30.types/type_system/_StmtCheck/bindings_check.spl:371` | `bind_pattern` (own params `pattern`, `ty`, `new_env`, recursive) | `pattern` (`Typed`) | `Typed` | (b) false positive (same-fn self-shadow, no reuse): `case Typed(pattern, ty_ann): new_env = bind_pattern(pattern, ty, new_env)` does rebind the function's own `pattern` param via destructuring, but the only code after this arm/match is `new_env` (the function's return value, line 397) — `pattern` itself is never read again in this or any later arm | left alone |
| `35.semantics/narrowing.spl:128` | `analyze_condition` (own params `cond`, `type_lookup`) | `op`,`left`,`right` (`Binary`) | `Binary` | (b) false positive: own params are `cond`/`type_lookup`, not `op`/`left`/`right`; `match cond.kind:` is the function's entire body (tail expression), so no arm's bindings are read post-match | left alone |
| `35.semantics/visibility_integration.spl:72` | `check_stmt_visibility` (own params `stmt`, `symbols`, `checker`) | `block` (`Block`) | `Block` | (b) false positive: own param `stmt`, not `block`; tail arm of the function's sole match | left alone |
| `50.mir/synthetic_driver_registration.spl:116` | `stmt_find_register_static_driver_call` (own params `stmt`, `symbols`) | `block` (`Block`) | `Block` | (b) false positive: own param `stmt`, not `block`; tail arm of the function's sole match | left alone |
| `60.mir_opt/mir_opt/loop_detect.spl:139` | `get_successors` (own param `term`) | `target` (`Goto`) | `Goto` | (b) false positive: own param `term`, not `target`; `case Goto(target): [target]` is one arm among several in the function's sole tail `match term:`, none of whose bindings (`target`,`then_`,`else_`,`normal`,`unwind`, etc.) collide with `term` or are read outside their own arm | left alone |
| `70.backend/backend/common/expression_evaluator.spl:72,75` | `eval_expr` (own params `expr`, `ctx`) dispatching to `eval_binary_op(op,left,right,ctx)` / `eval_unary_op(op,operand,ctx)` / `eval_call(func,args,ctx)` | `op`,`left`,`right` (`BinaryOp`); `op`,`operand` (`UnaryOp`); `func`,`args` (`Call`) | `BinaryOp`, `UnaryOp`, `Call` | (a) real, recurring instance of the `const_eval.eval`-family landmine: `eval_expr` is a recursive tree-walk dispatcher whose `BinaryOp`/`UnaryOp`/`Call` arm bindings are named identically to `eval_binary_op`/`eval_unary_op`/`eval_call`'s own parameters. Those methods call back into `self.eval_expr(left/right/operand, ctx)` to evaluate their subexpressions *before* reading their own `op`/`left`/`right`/`operand` params again (e.g. `eval_binary_op`'s `match op:` after both operands are evaluated); if a subexpression is itself `BinaryOp`/`UnaryOp`/`Call`, the recursive `eval_expr` re-enters this same dispatcher arm and rebinds `op`/`left`/`right`/`operand`/`func`/`args` under the identical names, which can corrupt the outer caller's own params under the interpreter's match-arm scoping leak | renamed dispatcher arm bindings `op,left,right`→`bin_op,bin_left,bin_right`; `op,operand`→`un_op,un_operand`; `func,args`→`call_func,call_args` |
| `70.backend/backend/interpreter.spl:706` | `exec_stmt` (own params `stmt`, `ctx`) | `block` (`Block`) | `Block` | (b) false positive: own params are `stmt`/`ctx`, not `block`; `case Block(block): self.eval_block(block, ctx)?; Ok(())` is the last arm of the function's sole match, nothing follows | left alone |
| `70.backend/backend/lean_borrow.spl:135,139` | `generate_place_definition` (own param `place`) | `idx` (`Field`, `ConstantIndex`) | `Field`, `ConstantIndex` | (b) false positive: own param is `place`, not `idx`; the bindings are local to a `for proj in place.projections:` loop body and never read outside that loop iteration — the code after the loop (`proj_list`, final `"Place.mk {place.base_id()} {proj_list}"`) reads `place`/`proj_parts`, never `idx` | left alone |
| `70.backend/linker/mold.spl:333` | `LinkerError.to_string` (own params: none, `self` only) | `code`,`stderr` (`ExitFailure`) | `ExitFailure` | (b) false positive: no parameters to collide with; `match self:` is the entire function body (tail expression) | left alone |

All 14 not-yet-triaged candidates from lane SHDW1 are now resolved by lane
SHDW2 (2026-07-30): 13 confirmed false positives (own-function param doesn't
match the arm binding, and/or the arm is the tail expression of a `match` that
is itself the function's entire body, so nothing observes a stale binding);
1 confirmed real and fixed (`expression_evaluator.spl`, a recurring instance
of the same recursive-dispatcher-with-identically-named-params shape already
fixed once in `const_eval.spl`). The sweep is now COMPLETE for the file list
enumerated in the original SHDW1 pass.

### Lane SHDW2 files changed (1)
`src/compiler/70.backend/backend/common/expression_evaluator.spl` — renamed
`eval_expr`'s `BinaryOp`/`UnaryOp`/`Call` dispatcher arm bindings
(`op,left,right`→`bin_op,bin_left,bin_right`; `op,operand`→`un_op,un_operand`;
`func,args`→`call_func,call_args`). Mechanical rename only, no logic changes.

### Lane SHDW2 spec verification
- `test/01_unit/compiler/backend/expression_evaluator_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/semantics/const_eval_spec.spl`: `Results: 2 total, 2 passed, 0 failed`
- `test/01_unit/compiler/semantics/resolve_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/deep/type_inference_unify_1_spec.spl`: `Results: 15 total, 15 passed, 0 failed`
- `test/01_unit/compiler/async/async_mir_interpreter_spec.spl`: `Results: 10 total, 10 passed, 0 failed`

### Files changed (24)
`src/compiler/20.hir/inference/unify.spl`,
`src/compiler/30.types/bidir_phase1{a,b,c,d}.spl`,
`src/compiler/30.types/bidirectional_inferencer.spl`,
`src/compiler/30.types/type_infer/inference_expr.spl`,
`src/compiler/30.types/type_system/bidirectional.spl`,
`src/compiler/35.semantics/const_eval.spl`,
`src/compiler/35.semantics/resolve.spl`,
`src/compiler/60.mir_opt/mir_opt/simd_lowering.spl`,
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`,
`src/compiler/70.backend/backend/common/type_mapper.spl`,
`src/compiler/70.backend/backend/cranelift_type_mapper.spl`,
`src/compiler/70.backend/backend/interpreter_type_mapper.spl`,
`src/compiler/70.backend/backend/llvm_type_mapper.spl`,
`src/compiler/70.backend/backend/wasm_type_mapper.spl`,
`src/compiler/70.backend/backend/native/isel_{x86_64,aarch64,riscv32,riscv64}.spl`,
`src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl`,
`src/compiler/70.backend/backend/vhdl_entity_compile.spl`,
`src/compiler/95.interp/mir_interpreter.spl`.
All renames are mechanical (arm-binding rename only; no logic changes).

### Spec verification (all green, or pre-existing failures confirmed via
side-by-side original-vs-patched runs so no regression was introduced)
- `test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl` + `mir_ssa_phi_intrinsic_spec.spl` + `test/01_unit/compiler/interp/strict_interp_spec.spl`: `Results: 6 total, 6 passed, 0 failed`
- `test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl` + bootstrap shared-binding-contract specs + `vhdl_subprogram_spec.spl`: `Results: 21 total, 1 passed, 20 failed` — **confirmed pre-existing**: identical 21/1/20 with the original (pre-rename) file content, re-verified byte-for-byte after restoring the patch
- `test/01_unit/compiler/type_inference/bidir_check_spec.spl`: `Results: 24 total, 24 passed, 0 failed`
- `test/01_unit/compiler/type_inference/bidir_type_check_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/type_inference/bidirectional_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/type_infer_link_contract_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/type_inference/expr_inference_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/type_inference/type_infer_comprehensive_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/type_inference/integration_simple_spec.spl`: `Results: 2 total, 2 passed, 0 failed`
- `test/01_unit/compiler/semantics/const_eval_spec.spl`: `Results: 2 total, 2 passed, 0 failed`
- `test/01_unit/compiler/backend/llvm_type_mapper_spec.spl`: `Results: 4 total, 4 passed, 0 failed`
- `test/01_unit/compiler/backend/type_mapper_spec.spl`: `Results: 4 total, 3 passed, 1 failed` — **confirmed pre-existing** (identical with original files)
- `test/01_unit/compiler/wasm_codegen_spec.spl`: `Results: 34 total, 33 passed, 1 failed` — **confirmed pre-existing** (identical with original files)
- `test/01_unit/compiler/backend/native/isel_x86_64_spec.spl`: `Results: 3 total, 3 passed, 0 failed`
- `test/01_unit/compiler/backend/native/isel_aarch64_spec.spl`: `Results: 5 total, 5 passed, 0 failed`
- `test/01_unit/compiler/backend/native/isel_riscv32_spec.spl`: `Results: 37 total, 37 passed, 0 failed`
- `test/01_unit/compiler/backend/native/isel_riscv64_spec.spl`: `Results: 42 total, 42 passed, 0 failed`
- `test/01_unit/compiler/backend/llvm_mutable_global_static_spec.spl`: `Results: 5 total, 5 passed, 0 failed`
- `test/01_unit/compiler/backend/llvm_lib_backend_spec.spl`: `Results: 5 total, 3 passed, 2 failed` — **confirmed pre-existing** (identical with original `core_codegen.spl`)
- `test/01_unit/compiler/backend/llvm_copy_move_alloc_spec.spl`: `Results: 6 total, 5 passed, 1 failed` — **confirmed pre-existing** (identical with original `core_codegen.spl`)
- `test/01_unit/compiler/backend/llvm_comparison_operand_type_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl`: `Results: 11 total, 4 passed, 7 failed` — **confirmed pre-existing** (identical 11/4/7 with the original `resolve.spl`)
- `test/01_unit/compiler/semantics/resolve_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/compiler/type_checker/type_inference_v2_spec.spl`: `Results: 70 total, 70 passed, 0 failed`

### Surprises
- The scanner's own paren-matching bug (fixed mid-sweep) is itself an instance
  of "measure the primitive first" — the first ~1163-hit run was almost
  entirely scanner noise from mis-detected function boundaries, not real
  collisions; every subsequent number in this doc is from the *post-fix*
  scanner.
- Several of the confirmed-real hits (`const_eval.eval`, `resolve.resolve_call_args`/`resolve_block`, the 5 `map_type` backends, the 4 `isel_*_lower_operand` backends) are **not** rare edge cases — they trigger on completely ordinary nested expressions (nested binary/call const-exprs, nested function/array types, a call passed as a call argument, an `if`/nested-block as a function's trailing expression). This looks like the same landmine family is latent throughout most of the compiler's recursive tree-walk passes, not just the one CUDA backend arm SIGF fixed.
- Two pre-existing, unrelated failing spec suites (`vhdl_design_catalog`-family and `resolve_nil_guard_spec.spl`) were verified NOT caused by this sweep only by literally restoring the original file bytes and re-running side-by-side — a cheap habit worth keeping for any rename-only change in a shared, red-baseline repo.
