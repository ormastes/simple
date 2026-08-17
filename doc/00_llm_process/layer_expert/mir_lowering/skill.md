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

0. **Bare match identifiers need value-before-capture resolution:** flat HIR
   represents `case NAME:` as `HirPatternKind.Binding` whether `NAME` is a
   fresh capture or a current-module scalar `val`. `lower_match_case` must
   first consult `builder.module.constants`, normalize exact int/bool/text
   constants to literal patterns, and dispatch `norm_arms`. Only an unresolved
   name remains an irrefutable capture. Text patterns compare by content with
   `rt_text_eq_any`, never by pointer identity. Regression:
   `test/01_unit/compiler/codegen/match_bare_val_constant_spec.spl`.

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

### Iso ownership: `emit_move` had exactly one caller before `6a53442f` (2026-08-06)

`MirBuilder.emit_move` (`src/compiler/50.mir/mir_data.spl:353`) previously had
exactly ONE call site in the whole compiler — the variable-to-variable
let-binding at `mir_lowering_stmts.spl:743`. Every other ownership transfer of
an `Isolated`-typed value (call argument, reassignment, field store, array/dict
element store) emitted a plain Copy, so the borrow checker (see
[layer_expert/borrow_check/skill.md](../borrow_check/skill.md)) never saw a
Move fact for them. Five more sites were added:

- Call argument — `_MirLoweringExpr/switch_operators_calls.spl`, `lower_call`,
  a `case HirTypeKind.Isolated(_):` arm.
- Reassignment `b = a` — `mir_lowering_stmts.spl`, `lower_assign_var` plain
  (non-compound) branch.
- Field store `o.f = a` — `Field` arm of the same assign path.
- `arr[i] = a` and `d[k] = a` — `Index` arm.

**Non-obvious trap:** element stores (`arr[i] = a`, `d[k] = a`) are NOT a
Store-instruction family — they lower to runtime CALLS (`rt_array_set` /
`rt_dict_set`) carrying bare operands. An earlier audit grepped
`MirInstKind.Store|emit_store|SetField|StoreField|StoreIndex` and found
nothing there, wrongly concluding the site didn't exist. Since there's no
instruction to hang a Move on, a synthetic `emit_move` into a fresh local is
inserted ahead of the call instead.

All five sites keep the original let-binding guard's two conditions: move
only on a PLACE read of an existing binding (`val b = a`), never on a fresh
construction (`val p = Point(x:1)`); and only in the plain, non-compound
assignment case. Predicate: `mir_hir_type_is_isolated` at
`mir_lowering_stmts.spl:48`.

Still open (lowering side, tracked in
`doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`):
no Move is emitted ahead of `Ret`, and `list.push(x)` has the identical gap at
`_MirLoweringExpr/method_calls_literals.spl:874`.

**Also unblockable, don't re-walk it:** the iso **struct**-field binding TODO
at `mir_lowering_stmts.spl:664-672` is UNREACHABLE, not merely unimplemented —
`find_local_hir_type(x) == Isolated` and `struct_value_syms.get(x) != nil` can
never co-occur, because `_MirLowering/function_lowering.spl:206` (records
`Isolated`) and `:239` (sets `struct_value_syms`) match mutually-exclusive
variants of the same `param.type_.kind`. Unblock condition: `:239` must
unwrap `Isolated` before its `Named` check. An agent implemented the TODO,
measured identical spec results before/after, and correctly REVERTED rather
than ship dead code.

Emission (this layer) and detection (`55.borrow`) are independent — neither
substitutes for the other, proven by isolation (disabling one alone re-breaks
only its own test case). See
[feature_expert/iso_ownership/skill.md](../../feature_expert/iso_ownership/skill.md)
for the end-to-end picture and specs.

**Working practice:** compiler `.spl` edits under `src/compiler/**` are LIVE
under `bin/simple test` — the test runner's interpreter loads source
directly, so no bootstrap rebuild is needed to iterate on this layer. That
says nothing about the compiled/JIT path or `bin/simple run` (seed).

### Span-bridge SIMD intrinsics missing from self-hosted MIR/LLVM (fixed, 2026-08-07)

`rt_engine2d_simd_fill_span_u32`/`copy_span_u32` (and, in a follow-up,
`blend_span_u32`/`blend_const_span_u32`) replaced the older row-based SIMD
span primitives in the interpreter and `backend_software.spl`, but the
native/AOT compilation path was never updated to match: MIR lowering's
`bootstrap_resolved_call_return_type` didn't register their `[u32]` array
return type (defaulted to i64, would corrupt the array on read), and the LLVM
backend had no `declare` for either symbol (link failure under AOT/JIT).
Fixed by registering all four alongside their row-based predecessors in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` and adding
their `declare ptr @...` lines in
`src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl`
(`a399483d` for fill/copy, `796d8484` for blend — the blend pair also needed
the native-ABI symbols added to the runtime crate first, `ccf1b9f4`, since
`engine2d_simd_ops.rs` — not the dead `runtime_simd_dispatch.c` — is what
actually links). **Pattern for any future span-primitive addition:** the
runtime symbol landing alone is not sufficient; this layer's array-return-type
registration and the backend's `declare` are a separate, easily-missed step —
grep both files for the sibling row-based symbol's registration line as the
template. See [ui_render layer expert](../ui_render/skill.md) for the
Engine2D/pixel-kernel perspective on the same landing.

### JIT: named-function-as-value bypassed the lambda-only closure-ABI guard (fixed, 2026-08-07)

Defect 2 of the JIT closure-ABI family (`jit_closure_abi_refuses_lambdas_and_
miscompiles_fn_refs_2026-08-06.md`): a named function passed as a bare value
(no lambda literal) bypassed the existing lambda-only JIT guard and hit the
same closure-ABI break in `compile_indirect_call`, producing an ASLR-shaped
garbage `i64` with **exit 0 and no diagnostic** — silent miscompile, not a
crash. Fixed in the Rust seed JIT (`src/compiler_rust/compiler/src/codegen/
jit.rs`, `Self::first_named_fn_value_load`): detects a `MirInst::GlobalLoad`
whose name is a declared function but not a declared global (the shape
`lower_global_expr`'s "static method reference" fallback emits) and refuses
the module, matching Defect 1's existing loud interpreter-fallback shape
instead of miscompiling. Verified against the full `jit_closure` fixture set
(f01-f09): f06 goes from silent garbage to a loud `[INFO]` fallback + correct
42; f01/f09 (no-fallback controls) unaffected, confirming no over-refusal of
ordinary calls. This is JIT-codegen-layer, not MIR-lowering proper, but sits
next to the SIMD-ISA-gating JIT note above in the same Rust seed codegen
surface — see that entry for the sibling "silent wrong output, not a crash"
failure shape in this file family.

### `struct_value_syms` provenance registration: every struct-value-producing site must register (2026-08-07)

`struct_value_syms` (`Dict<LocalId, text>`, `expr_dispatch.spl`) is the
provenance map `resolve_field_index` and friends fall back to when a struct
value's static HIR type is missing/erased — keyed by the producing local's
id, valued by the struct's name. The convention: **any lowering site that
produces a struct-typed SSA value must register that value's local id in
`struct_value_syms`** (construction, nested-struct-field reads, dict-decoded
structs, binop results propagating a struct operand, unwrap of `!`/`.unwrap()`
on a struct-typed optional, etc. — see the call sites at `expr_dispatch.spl:229,
390, 1045, 1334, 1651, 2526, 3080, 3211, 3309`).

`try_lower_global_read` (`expr_dispatch.spl:202`) was the one struct-value-
producing site that did **not** register — it read a global's HIR-typed value
without adding a `struct_value_syms` entry for the resulting local. Fixed in
`606bae83998` (+19 lines). **When adding or auditing a new lowering arm that
can produce a struct value, check it registers `struct_value_syms` on its
result local** — grep `struct_value_syms\[.*\] =` in this file for the
existing pattern to follow.

**Probe technique — `SIMPLE_MIR_FIELD_TRACE=1`:** set this env var to trace
field-read/global-read lowering decisions at `expr_dispatch.spl:218,1046` and
`function_lowering.spl:1068`. Used as a **discriminating** probe (not just a
log dump) to test the struct-provenance-gap hypothesis for the aarch64
`@repr("C")` global-struct field misread — see next entry.

**Refuted-hypothesis note:** the `try_lower_global_read` gap fixed above was
suspected as the CAUSE of the aarch64 real-firmware `@repr("C")` global-struct
field-read defect, but the `SIMPLE_MIR_FIELD_TRACE=1` probe REFUTED that:
x86_64 JIT already covers the read via the HIR-type fallback, independent of
`struct_value_syms`. The fix is still correct/worth keeping (closes a real
provenance gap for other callers), but it is not the aarch64 root cause.
Surviving candidates for the aarch64 defect: Cranelift `GetField`'s uniform
8-byte field stride, and an unconditional `band(addr, -8)` tag-strip applied
regardless of field alignment. Verifying either is blocked on the tracked
native-build SIGSEGV (see `layer_expert/os_kernel_exec/skill.md` and
`doc/08_tracking/bug/mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`).
Full writeup + probe transcript:
`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`.
New regression spec: `test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl`.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`

## Never identify the builtin `Option` by NAME (2026-08-16, from `8d96687c991`)

Match lowering must separate two things that share a name:

| | Builtin `Option<T>` | User-declared `enum Option` |
|---|---|---|
| Runtime shape | nil-boxing | ordinary allocated enum object |
| Identity | reserved enum id `OPTION_ENUM_ID` = **1** | ordinary dynamically assigned id |
| Correct path | optional fast path (`rt_is_none`/`rt_is_some`) | discriminant path |

Both register as `HirType::Enum` named `"Option"` owning `Some`/`None`, so the
**name cannot distinguish them**. Both runtimes key on the id and nothing else —
`runtime/src/value/objects.rs:490` (`enum_id == OPTION_ENUM_ID`) and
`src/runtime/simple_core/core_values.spl:61` (`if rt_enum_id(value) != 1`).

`8d96687c991` added a builtin-`Option` exception keyed on `name == "Option"` plus
the 2-variant `Some(payload)`/`None` shape. That matches user enums too, and
misroutes them:

- `case Option::Some(v)` → `rt_is_some(obj)` → `!rt_is_none(obj)`; obj is
  non-nil and `enum_id != 1`, so it is **unconditionally true — irrefutable**,
  and the early return fires before payload handling, **dropping the binding**.
- `case Option::None` → `rt_is_none(obj)` → `enum_id != 1` → **never matches**.

This is exactly what `subject_enum_owns_variant` was introduced to prevent; its
own comment records the original symptom as *"made `case Some(x)` irrefutable
and bound x = 3"*.

### Rules

1. **Key on the reserved enum id, never the name string.** If the id is not
   reachable at the decision point, thread it there. A name test can only be
   narrowed, never made correct — a user enum may legally take that name and shape.
2. **The predicate lives in TWO places that must agree** —
   `hir/lower/expr/control.rs` and `hir/lower/stmt_lowering.rs`, ~14 lines
   duplicated verbatim, held in sync only by a comment. Change both; prefer one
   shared helper.
3. **Any fence for this class must be a NATIVE lane.** The tree-walk interpreter
   binds match arms from `HirFunction` directly and reports green against a
   broken compiler.

Reachable in-tree: `driver/tests/runner_tests.rs:851,870,892`
(`runner_handles_option_type`, asserting 42 and 99) and
`src/compiler/30.types/bidirectional_types.spl:105`.

Bug: `doc/08_tracking/bug/seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16.md`.
Fence: `test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl`
(fail-closed, unexecuted — no qualified pure-Simple runtime exists).
Guide: `doc/07_guide/language/user_option_enum_match_lowering.md`.
