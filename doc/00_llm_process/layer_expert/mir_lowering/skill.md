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

3. **Empty-literal element-type erasure:** `var d = {}` / `var a = []` fix the
   container's MIR element type at the i64 default; stores box by VALUE type
   but reads/print/`==` decode by CONTAINER type, so a later f64 store leaked
   the heap-box pointer as an int. `runtime_elem_value_type` (id-keyed, reset
   with `runtime_dict_locals`) records the store-observed F64/F32 type; reads
   consult it only when the static element type is the erased i64 default
   (see `note_container_elem_type` in expr_dispatch.spl). Text values through
   the same path SIGSEGV — pre-existing, see
   `doc/08_tracking/bug/native_empty_dict_text_value_sigsegv_2026-07-20.md`.
4. **Never hand-duplicate the `MirLowering(...)` ctor** (driver_pipeline did,
   twice): the seed interpreter silently nil-fills omitted struct-init fields,
   so a drifted copy crashes with `method has not found on type nil` — native
   path only. Always call `MirLowering.new_for_target`.

## `lower_type` wildcard arm — verify new `HirTypeKind` variants get real arms

`_MirLowering/function_lowering.spl`'s `lower_type` match had only 17 of 26
`HirTypeKind` variants (declared `src/compiler/20.hir/hir_types.spl`) with
explicit arms; 9 fell through to a FATAL `case _:` wildcard (`Slice,
TypeParam, DynTrait, Function, Projection, Isolated, Any, Tensor, Layer`),
aborting compilation for any code touching those types. **When adding a new
`HirTypeKind` variant, or when a "MIR lowering error" names a type kind you
don't recognize, check `lower_type`'s arm list against the current
`HirTypeKind` declaration first** — a wildcard match hiding missing variants
is a silent trap that only surfaces when someone's code happens to use the
gap. See `doc/08_tracking/bug/mir_lowering_missing_hirtypekind_arms_wildcard_fatal_2026-08-05.md`.

## Update Rule

After changes to method lowering, array handling, or runtime_array_locals
registry, refresh this skill with new patterns and any regressions found.

## Array-loss RCA pinpoints + pending fix drafts (2026-07-26)

The freestanding array-loss class is pinpointed: array-typed module globals
emit no `MirStatic` (`module_lowering.spl:62-81` rejects array types) →
writes degrade to SSA locals (`mir_lowering_stmts.spl:794` write hook needs
`find_global_static`) → reads RE-LOWER the initializer
(`expr_dispatch.spl:190-192`, 952d2ca34d7's immutable-only fallback
violated by mutation). Nested-array returns lose runtime-array identity for
array-typed elements (`expr_dispatch.spl:1094-1139` registers named structs
only); `SIMPLE_BOOTSTRAP=1` forces underivable element types to `text`
(`:1084-1085`). Also: `match case Some(x)` never learned Option's FLAT
raw-or-nil lane (`Dict.get` is correct; the decoder is not) and the
interpreter's `match_pattern` had no enum-variant case at all. Fix drafts
(A1+B2, match-decoder) exist in the 2026-07-26 session scratchpad — each
needs bootstrap + extended smoke. Full evidence:
`doc/08_tracking/bug/cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`.

### Hand-inlined SIMD intrinsics in the Rust seed must gate on target ISA (2026-08-06)

`src/compiler_rust/compiler/src/codegen/instr/calls.rs` has hand-written
inline-codegen fast paths for a few numeric SFFI intrinsics
(`compile_inline_numeric_contains_u64`, `compile_inline_numeric_xor_sum_u64`)
that emit explicit Cranelift `I64X2` SIMD ops (`splat`/`load.i64x2`/`bxor`/
`vany_true`). These previously emitted unconditionally on every target,
including riscv64 without the `V` extension, where
`ty_supported_vec`/`min_vec_reg_size()` is `0` — no vector type of any lane
width can lower there, so this crashed codegen with "should be implemented in
ISLE" (looked like a missing lowering rule; it was compiler-side
overgeneration, not a real ISA gap — there's no vector hardware to add a rule
for). Fixed by gating the SIMD fast path to `Architecture::X86_64` /
`Aarch64(_)` (guaranteed SSE2/NEON) and falling back to a plain scalar loop
everywhere else. Any new hand-inlined SIMD intrinsic in this file needs the
same `ctx.module.isa().triple().architecture` check — grep `I64X2\|I8X16\|
I32X4\|vany_true\|vall_true` in that file before adding a target. Full
writeup: `doc/08_tracking/bug/riscv64_kernel_codegen_blocker_2026-07-20.md`.

### `Array.first()`/`.last()` MIR lowering never engaged (2026-08-06)

Real MIR lowering for `Array.first()`/`.last()` under native codegen was added
(`c49bb5606de`), but a later execution-verify pass found it still did not
engage at runtime — the lowering was missing the `Some(...)` wrap the caller
expected, so the fast path silently fell through (`21875c735e1` diagnosis →
`1692ceb0b9a` fix). **Execution-unverified as of this session** — the fix
landed but a re-test was blocked by the separate `SymbolTable.lookup` nil-scope
crash (see `layer_expert/bootstrap/skill.md`) preventing a clean rebuild. Do
not cite this as confirmed-working without re-running once that blocker
clears.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
