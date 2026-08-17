# `native-build --backend llvm`: every user function using `return` silently returned 0

- **Date:** 2026-08-01
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** Critical — silent wrong answer, exit 0, real ELF, no diagnostic
- **Area:** `src/compiler/20.hir/hir_lowering/`, `src/compiler/70.backend/backend/_MirToLlvm/`
- **Lane:** `bin/simple_seed native-build <file>.spl --backend llvm` (the pure-Simple
  compiler interpreted by the Rust seed). The seed's own interpreter (`simple run`)
  is NOT affected — it never goes through this HIR/MIR/LLVM path.

## Summary

Any user-defined function whose value left the body through an explicit `return`
statement compiled to `ret i64 0`. Inline arithmetic in the entry function was
correct, so the failure was invisible except as zeros appearing through every
function boundary. Exit code 0, a real ELF, no error, no interpreter-fallback
notice.

A second, independent defect made a function that returns a *named local* (via a
MIR `Copy`) also emit `ret <ty> 0`, even on the tail-expression form.

Measured, LLVM native lane, identical program before/after:

| source form | before | after |
|---|---|---|
| `fn add(a,b) -> i64: return a + b` | **0** | 5 |
| `fn add(a,b) -> i64: a + b` (tail) | 5 | 5 |
| `fn const42() -> i64: return 42` | **0** | 42 |
| `fn f1(a) -> i64: val x = a*2; return x` | **0** | 10 |
| `fn f2(a) -> i64: if a>0: return 111; return 222` | **0 / 0** | 111 / 222 |
| `fn f3(a) -> i64: val y = a+1; y` (tail of a local) | **0** | 6 |
| `fn f4() -> text: return "hello"` | **empty** | hello |
| `fn f5() -> text: "world"` (tail literal) | world | world |

The emitted IR for the RED case (captured with `SIMPLE_KEEP_LLVM_IR=1`):

    define i64 @add(i64 %l1, i64 %l2) nounwind readonly alwaysinline {
    bb0:
      ret i64 0
    }

The call site was always correct (`mov $2,%edi; mov $3,%esi; call add; mov %rax,%rbx`),
so this was neither a call-site nor a register-ABI bug — the callee body was empty.

## Root cause 1 (the big one): `case Some(...)` matched against a plain nullable

`src/compiler/20.hir/hir_lowering/statements.spl`, the disc-guarded
`StmtKind.Return` fast path (which SHADOWS the ordinary `case StmtKind.Return`
arm further down the same function):

    val rt_val: Expr? = ...            # correctly holds the returned expression
    val rt_hir: HirExpr? = match rt_val:
        case Some(rt_val_e): self.lower_hir_expr(rt_val_e)
        case _: nil                    # <-- ALWAYS taken

`rt_val` is a plain NULLABLE `Expr?`, not an `Option` box, so `case Some(...)`
never matches it on this lane. Every `return <expr>` therefore lowered to
`HirExprKind.Return(nil)`, MIR produced `Ret(nil)`, and the LLVM backend
faithfully emitted the documented "no value" `ret <ty> 0`.

Proved with a level-gated probe (`SIMPLE_MIR_RET_TRACE=1`):

    [hir-ret-fast] ast_nil=false hir_nil=true     # value present in AST, dropped in HIR
    [llvm-ret-top] fn=f1 value_nil=true           # backend sees Ret(nil)

**Fix:** bind with `if val`, the repo idiom for nullables.

This is the same defect family as
`.claude/memory/reference_case_some_on_nullable_never_matches.md`; that fix
landed elsewhere, this call site was missed. *A sweep that does not enumerate the
family leaves siblings.*

## Root cause 2: `Copy` destinations were never marked defined

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`.
`translate_instruction` has disc-guarded fast paths for `Const` and `Copy` that
`return` early — before the trailing `self.mark_instruction_dest_defined(inst)`
call at the bottom of the method. `translate_const` sets `defined_locals` itself,
so `Const` was covered; `translate_copy_move` did not, so **no Copy destination
was ever recorded as defined**. `translate_terminator`'s not-defined guard then
fired and emitted `ret <ty> 0` for any function returning a named local:

    if self.return_locals.has(id) or not self.local_types.has(id) or not self.defined_locals.has(id):
        emit ret <ty> 0

Probe output: `[llvm-ret] fn=f3 local=4 is_return_local=false has_type=true defined=false`.

**Fix:** set `self.defined_locals[dest_id] = true` in `translate_copy_move`, at
the value-defining site, so the fast path and the `Move` arm agree.

Both fixes are required: with only fix 1, `f1`/`f3` still returned 0.

## Verification (PROVED)

RED baseline was re-measured on pristine origin content for both files
(`git show <origin-tip>:<path>`), then the fixes were restored and re-measured on
the same tree — an A/B with only these two files toggled. Positive artifact: a
built ELF printing distinctive non-zero values derived through function calls
(`f2a=111 f2b=222 fact=120 outer=120`).

Family sweep on the fixed lane (all correct): 5-argument function, `bool`, `f64`,
`text`, struct-by-value return, direct recursion (`fact(5)=120`), nested calls,
class methods (`me` and non-mutating), and both explicit-`return` and
tail-expression forms. `fn main() -> i64` now propagates its returned value to
the process exit code (`return t` where `t==5` exits 5); before the fix it
exited 0.

`scripts/check/native-smoke-matrix.shs` must be run with
`SIMPLE_BINARY=bin/simple_seed` — its default `bin/simple` crashes on
`native-build` (`runtime error: field access on nil receiver`), so the default
invocation reports nothing about this lane. With the seed it is very slow
(~5 min/case, each case rebuilds the pure-Simple compiler under the seed
interpreter with `--clean`). Full run on the fixed tree, **15 PASS / 8 build-fail**,
`fallback_hits=0` on every case:

    PASS  1 arith_fn_call(7)   2 if_elif_else(3)   5 array_index_rw(71)
          6 struct_field(71)   7 enum_construct(42) 9 string_concat_len(6)
         10 string_interp(7)  11 nested_fn_3deep(7) 13 dict_index(7)
         14 option_nil_check(7) 16 match_value_position(7)
         17 match_value_position_return(7) 18 trait_default(42)
         21 tuple_return_across_call(42) 23 parse_f64(42)
    FAIL  3 while_sum   4 for_in_array   8 enum_match*   12 closure_lambda*
         15 result_try_op*  19 dict_struct_value  20 enum_f64_payload_precision
         22 hyphenated_module_init      (* = documented XFAIL in the script header)

Every PASS case above checks a value carried out of `fn main() -> i64` by an
explicit `return`; all of them would have exited 0 before this fix.

Cases 3, 4, 20 and 22 were re-measured on pristine pre-fix content and fail
IDENTICALLY (`build-failed`) there — pre-existing, not regressions. Case 19 is
the one behaviour change, and it moves in the safe direction: pre-fix it BUILT
and returned **0** (silent wrong answer, want 73); post-fix it fails to build
loudly (see below).

## Adjacent gaps found, NOT caused by this bug (pre-existing, reproduced on
## pristine origin content)

- `unresolved method call: merge` in MIR lowering. Reproduced identically on
  pristine origin content in every case below — pre-existing, not a regression.
  Two shapes hit it:
  - a `me` method that MUTATES a field and then returns it
    (`self.n = self.n + d; return self.n`);
  - a `while` loop whose accumulator is then returned — this is exactly
    `native-smoke-matrix.shs` case 3 (`while_sum`), which fails to BUILD.
  A `while` loop on its own is fine (`var i = 0; while i < 3: i = i + 1` builds
  and prints 3), and so is a returned mutated `var` without a loop
  (`var t = 0; t = t + 5; return t` exits 5), so it is the combination.
- **Duplicate `%tN` SSA definition on a tagged aggregate base (NOT FIXED —
  deliberately left loud).** Smoke case 19 (`dict_struct_value`, `#189`) now
  fails with `llc-18: error: multiple definition of local value named 't7'`. The
  emitted IR is:

      %t7 = inttoptr i64 %l33 to ptr
      %t7 = ptrtoint ptr %t7 to i64        ; same %tN defined twice

  Root cause (PROVED by fixing it experimentally): in
  `_MirToLlvm/aggregate_intrinsics.spl`, `translate_get_field` (and
  `translate_set_field`) inline an EMITTING call in the argument position —
  `self.untag_aggregate_base_ptr(self.value_as_type(...))`. `value_as_type`
  emits the `inttoptr` and advances the builder's fresh-local counter, but that
  counter bump is lost across the receiver-method call boundary
  (copy-modify-reassign `self` semantics on this lane), so
  `untag_aggregate_base_ptr`'s first `fresh_local()` hands back the same `%t7`.
  Hoisting the argument into its own `val` before the call makes case 19 build.

  **Not landed on purpose.** With the hoist applied, case 19 builds and returns
  **63 instead of 73** — `.y` reads `.x`'s word, i.e. the separate, already-known
  struct-valued-`Dict` field-offset defect (`#189`, and the standing "never call
  `.get()` on a dict whose value type is a struct" rule). Landing the hoist alone
  would convert a loud `llc` rejection into a silent wrong answer, which is the
  wrong direction. Whoever fixes `#189` should apply the hoist in the same change;
  it is regression-free on its own (`f1..f5` and struct construct + field read
  stay correct with it applied).
- Lambdas/closures fail this lane with `MIR lowering error: undefined variable: z`.
- `--backend c` is rejected outright: "native-build backend 'c' is not available
  in the pure Simple command path". LLVM is the only usable native-build backend
  here, so this defect had no working sibling lane to cross-check against.
- The self-hosted `bin/simple` (not the seed) crashes with
  `runtime error: field access on nil receiver` on `native-build`, so the seed is
  currently the only way to exercise this path.

## Debug probes added (level-gated, default OFF)

- `SIMPLE_MIR_RET_TRACE=1` — `[hir-ret-fast]` in `statements.spl`: whether the
  AST return value survived into HIR.
- `SIMPLE_LLVM_RET_TRACE=1` — `[llvm-ret-top]` / `[llvm-ret]` in
  `core_codegen.spl`: whether the backend saw a value on `Ret`, and which of the
  three zero-fallback conditions fired.
- `SIMPLE_KEEP_LLVM_IR=1` (pre-existing) keeps `/tmp/simple_llvm_<pid>.ll`.

---

# Follow-up lane: `#189` fixed, and the hoist landed with it

- **Date:** 2026-08-01 (same day, follow-up lane)
- **Status:** FIXED — smoke case 19 (`dict_struct_value`) now BUILDS and returns **73**
- **Area:** `src/compiler/50.mir/_MirLoweringExpr/`,
  `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`
- **Engine scope:** native LLVM only. The seed's JIT and interpreter were
  measured clean on every shape below (see the engine matrix).

The section above deliberately left the `%tN` hoist unlanded, because applying
it alone turned a loud `llc` rejection into a silent wrong answer (63 instead of
73). That trade is now unnecessary: `#189` is fixed, so the hoist and the fix
land together and case 19 both builds and returns the right value.

## Reproduction of the handoff state (PROVED)

Measured in an isolated scratch extraction of pristine origin `5ca84bcefe5`
(`git archive` into a scratch dir; `bin/simple_seed native-build` resolves
`src/compiler/**` relative to CWD, so this is a fully isolated A/B lane and the
shared working copy was never touched).

| tree state | case 19 result |
|---|---|
| pristine origin `5ca84bcefe5` | **build-fail**: `llc-18: error: multiple definition of local value named 't7'`, exit 1, no ELF |
| + hoist only | builds, exit 0, real ELF, returns **63** (`.y` read `.x`) |
| + hoist + `#189` fix | builds, exit 0, real ELF, returns **73** |

## Root cause of `#189`

`resolve_field_index` (`50.mir/_MirLowering/function_lowering.spl`) ends in
`0  # Default fallback when type is unknown`. When its whole lookup chain misses,
**every** field of the struct resolves to index 0, so the backend GEPs to word 0
for `.x` AND `.y`. The LLVM `getelementptr` in `translate_get_field` is correct
and *is* field-index-aware — the wrong index was handed to it.

The chain missed for a dict-read result for a precise reason. A level-gated probe
(`SIMPLE_MIR_FIELD_TRACE=1`) on the fixed lane shows it:

    [dict-read] base=3 decoded=33 arm=true sym_id=1000000000 sym_found=false ... aes='Point'
    [field-idx-fallback0] field=y base_local=38 in_svs=false

- `arm=true` — `lower_dict_runtime_read`'s existing `#189` guard
  (`case MirTypeKind.Struct(struct_symbol)`) DID match and bind. The dict value
  TYPE resolves correctly, which is why `decode_runtime_value` took its correct
  raw-passthrough arm and the struct's bits survived intact — and therefore why
  `.x` (field 0) always looked right and only `.y` was visibly wrong.
- `sym_id=1000000000`, `sym_found=false` — the numeric `SymbolId` carried in the
  MIR type does **not** resolve back to a named symbol via `get_symbol_raw` at
  this point in lowering. So the name was never written to `struct_value_syms`.
- `in_svs=false` — `resolve_field_index` consequently found no name-keyed
  provenance and fell through to `0`.

The previous `#189` attempt was therefore *present but inert*: it looked correct
and never fired. This is precisely the hazard `resolve_field_index`'s own leading
comment already warns about — "Numeric SymbolIds are local to each module and can
collide ... A lowered local's name-keyed provenance is therefore authoritative
when available."

## Fix

Use the name-keyed provenance the codebase already maintains.

1. **`expr_dispatch.spl`, `lower_dict_runtime_read`** — when the `Struct(symbol)`
   lookup yields no name, fall back to
   `array_element_struct_syms[<container local>]`. `note_container_elem_type`
   already writes the value's struct NAME there at every `d[k] = v` store, and
   the array Index-read path already consumes it; the dict read simply never did.
   (`aes='Point'` in the probe above: the right answer was sitting there unused.)

2. **`literals.spl` + `method_calls_literals.spl`, `lower_dict_lit`** — a dict
   born as a LITERAL (`{"k": Point(...)}`) is never stored into, so step 1 had
   nothing to read and `{"k": P(...)}["k"].y` was still wrong (**60**, want 70)
   even with step 1 applied. Capture the value's struct name off the raw local
   (before `box_runtime_value`, mirroring how `value_type` is already read) and
   register it on the dict local, exactly as `lower_array_lit` does for arrays.
   **These two `lower_dict_lit` definitions are byte-identical duplicates** —
   patched both so whichever wins dispatch carries the fix.

3. **`aggregate_intrinsics.spl`** — the hoist described in the section above,
   in BOTH `translate_get_field` and `translate_set_field`.

## Family sweep (enumerated, not sampled)

Native LLVM lane, `bin/simple_seed native-build --backend llvm`, each built and
RUN as a real ELF:

| shape | before | after |
|---|---|---|
| 2-field struct, `d[k] = v` store (case 19) | build-fail / 63 with hoist | **73** |
| 4-field struct, all four fields read | 229 (= 8421 mod 256) | **229 (= 8421 mod 256)** correct |
| nested struct `m[k].inner.q` | 40 | **40** correct |
| struct read via a local (`val p = m[k]; p.y`) | 70 | **70** correct |
| **dict LITERAL `{"k": Point(...)}`** | **60 (wrong)** | **70** |

The 4-field case is reported through the process exit code, which is mod 256:
`8421 mod 256 == 229`. The all-fields-read-as-field-0 wrong answer would be
`1+10+100+1000 = 1111`, i.e. `87` — so 229 distinguishes correct from wrong.

**Engine matrix.** The same five shapes (2-field, 4-field, nested, int-key,
text-field) were run on the seed's JIT (default `run`) and on the forced
interpreter (`SIMPLE_NO_JIT=1 run`): **all correct on both, before any fix**.
`#189` is native-LLVM-only — the interpreter never goes through
`resolve_field_index`. The standing rule "never call `.get()` on a dict whose
value type is a struct/class/enum" was written for this defect's neighbourhood;
the index-read half (`d[k]`) is what this change fixes.

## Debug probes added (level-gated, default OFF)

- `SIMPLE_MIR_FIELD_TRACE=1` — `[dict-read]` in `expr_dispatch.spl`
  (which resolution arm fired, the symbol id, whether it resolved, and the final
  struct name) and `[field-idx-fallback0]` in `function_lowering.spl` (every time
  `resolve_field_index` silently defaults a field to index 0 — the exact silent
  failure mode of this bug).
