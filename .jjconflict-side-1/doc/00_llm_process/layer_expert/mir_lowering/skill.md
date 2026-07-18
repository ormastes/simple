# mir_lowering Layer Expert

## Role

Own layer-specific process knowledge for MIR construction and lowering
(`src/compiler/50.mir/`). MIR is the intermediate representation between HIR
(typed AST) and backend (LLVM IR). Key phases: HIR→MIR lowering
(`_MirLowering/`), MIR SSA cleanup (`mir_opt/`), and MIR→LLVM codegen
(`backend/_MirToLlvm/`). This layer owns method-call/literal lowering, array
handling, struct construction, and intrinsic dispatch.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Layer Links

- HIR→MIR lowering: [src/compiler/50.mir/_MirLowering/](../../../../src/compiler/50.mir/_MirLowering/)
  (expr/stmt/item lowering).
- Method calls & literals: [src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl](../../../../src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl)
  (array construct/push/read/write, method dispatch).
- MIR SSA opt: [src/compiler/60.mir_opt/mir_opt/](../../../../src/compiler/60.mir_opt/mir_opt/)
  (var_reassign_ssa.spl, dead-code elimination).
- Backend codegen: [src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl](../../../../src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl).
- Unit specs: `test/01_unit/compiler/50.mir/` (e.g. `method_calls_literals_spec.spl`).

## Known Patterns (2026-07-10)

### Value-Array Discarded Push (silent no-op)

**Symptom:** `x.push(v)` in statement position (not assigned to a var) is a
silent no-op on native backend — array is val-bound (immutable by value), so
native codegen discards the result.

**Fix:** Rebind to a `var` and reassign:
```
var x = [1, 2]
x.push(3)  // native: silent no-op (x still [1, 2])
// Correct:
var x = [1, 2]
x = x.push(3)  // x now [1, 2, 3]
```

**File refs:**
- [src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl](../../../../src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl)
  (array_push lowering).

### runtime_array_locals Registry (id-keyed)

**Pattern:** Native path array construct/read/write uses `runtime_array_locals`
(module-global id-keyed registry in `src/runtime/`) to track array buffers.
Each construct gets a unique id; read/write/push marshal through that registry.

**Gotcha:** Parallel expr_dispatch/method_calls_literals rewrites can DROP
registry hunk presence. After any expr_dispatch refactor, re-verify:
- Construct: `make id -> runtime_array_locals.insert(id, buf)`.
- Read/Write: `runtime_array_locals.get(id) -> buf[i]`.
- Always check spec results — registry is NOT auto-verified by type-checker.

**File refs:**
- [src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl](../../../../src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl)
  (construct/read/write codegen).

## Gotchas

1. **Arrays are value types:** passed by copy, so `.push()` / `.pop()` /
   `.reverse()` return a new array (not mutating in-place). Statement-position
   calls are discarded on native (no side effect). Always assign or use in
   expression.
2. **Method dispatch collision:** if same method name has >1 candidate
   (`CODEGEN-AMBIGUOUS-METHOD`), typed local `val ct: T = x` in same function
   works; FOR-LOOP VAR annotations are ignored (need separate typed val in
   body). Local dict indexing erases to ANY. See
   [doc/00_llm_process/feature_expert/codegen_ambiguous_method/skill.md](../../feature_expert/codegen_ambiguous_method/skill.md).

## Update Rule

After changes to method lowering, array handling, or runtime_array_locals
registry, refresh this skill with new patterns and any regressions found.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
