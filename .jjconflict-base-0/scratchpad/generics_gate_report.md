# Task #158 Phase A — Generic Function Silent-Wrong -> Loud Fail (Native --entry path)

## Root cause (drop point)

`fn id<T>(x: T) -> T: return x` parses its `<T>` correctly (`parse_type_params()` in
`src/compiler/10.frontend/core/parser_decls_fn.spl`), and the flat-AST decl node
stores it correctly (`decl_type_params[idx] = type_params` in
`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:307`, readable back via
`decl_get_type_params(idx)` at `decl_nodes.spl:719`).

The drop happens in the flat-AST -> parser-AST bridge:

**`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`, `convert_decl_fn`
(original line 995)** — the call to `parser_function_new(...)` hardcoded the
`type_params` argument to a literal `[]`, discarding `decl_get_type_params(idx)`
entirely. So by the time HIR lowering (`lower_function` in
`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`) saw the
`Function` AST node, `fn_.type_params` was always empty — every existing
downstream check gated on `type_params.len() > 0` was dead code. `T` in the
param/return type then resolved through `lower_named_kind` as an
unrecognized/unresolved name and erased to `Infer`/`ANY`, so `id(42)` silently
returned 0 instead of 42 on the native `--entry` build path (build "succeeded",
answer was wrong, no diagnostic).

## Fix

1. **`convert_nodes.spl` (`convert_decl_fn`)** — build a real `[TypeParam]`
   list from `decl_get_type_params(idx)` (one `TypeParam` per captured name,
   empty bounds, `Infer` default) and pass it into `parser_function_new`
   instead of `[]`. (`convert_decl_extern_fn` and `convert_decl_method_fn`
   were left untouched — extern fns aren't in scope, and method_fn already
   forwards `base.type_params`, which now carries the real value.)

2. **`declaration_lowering.spl` (`lower_function`)** — after the existing
   type-param-lowering loop, added a hard gate: if `fn_.type_params.len() > 0`,
   call `self.error(...)` with a clear "generic functions are not supported on
   the native build path yet ... (#158 Phase B)" message. This is a
   *deliberate* hard stop for Phase A; real monomorphization is Phase B.

3. **`driver.spl` (`_hir_lowering_error_is_fatal`)** — **the surprise finding**.
   HIR lowering already has its own allowlist-downgrade mechanism, parallel to
   the MIR `_mir_error_is_fatal` one the task warned about: any
   `HirLowering.error()` push is fatal ONLY if the message starts with
   `"unresolved name:"`; everything else silently becomes a non-fatal warning
   (comment at driver.spl:97-114 documents this was deliberate, added for a
   prior "unresolved name" fix, because most `self.error()` calls are recovered
   internal noise, e.g. `Result` arity checks that don't actually break the
   build). Without extending this allowlist, my Phase A gate's error would have
   been silently downgraded to a warning and the build would have continued
   into monomorphize/MIR/LLVM anyway — which is exactly what happened on the
   first verification pass: it fell through to a cryptic `llc` failure
   (`void type only allowed for function results`, i.e. still a build failure,
   but with a useless diagnostic, at the wrong layer). Added a second
   allowlisted prefix, `"generic functions are not supported on the native
   build path yet"`, so the HIR-level error is genuinely fatal and surfaces at
   the phase-3 HIR/typecheck gate in `driver.spl` `compile()` (which returns
   `CompileResult.TypeError` and skips monomorphize/MIR/backend entirely).

Files touched (all in-scope, no forbidden files):
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
- `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`
- `src/compiler/80.driver/driver.spl`

## Battery results

| # | Test | Oracle (interp) | Native build | Notes |
|---|------|------------------|--------------|-------|
| 1 | `fn id<T>(x: T) -> T` + call `id(42)` | exit 0, prints `42` | **exit 1, no binary.** `error: HIR lowering error in ...: generic functions are not supported on the native build path yet: fn 'id' declares type parameter(s); monomorphization is not implemented (#158 Phase B)` | Loud fail confirmed at HIR/phase-3, before monomorphize/MIR/LLVM |
| 2 | `fn id<T>(x: T) -> T` declared, never called | n/a | **exit 1, no binary**, same message | Chose loud-fail-always (function is lowered regardless of call sites in this pipeline) |
| 3 | Control: `fn add(a: i64, b: i64) -> i64` + call | exit 0, prints `7` | exit 0 (build), runs, prints `7` | Oracle-equal, non-generic path fully unaffected |
| 4 | `struct Box<T>: val v: T`, `Box(v: 99)` | **Pre-existing, unrelated oracle bug**: interpreter/JIT fails with `HIR lowering error: cannot infer field type ... struct 'Box' field 'v'` / `class Box has no field named v` (reproduced on this exact commit, independent of this patch — neither touched file affects struct/field lowering) | build succeeds, runs, prints `99` (correct value) | Generic struct still builds via existing erasure path; not regressed by this change |
| 5 | Multi-construct (struct method + match-returning-text + lambda map) | Same pre-existing oracle struct-literal bug as #4 blocks a full run | Native build succeeds but a *separate pre-existing* bug surfaced: a plain (non-generic) `fn classify(n: i64) -> text` using `match`/`return "text"` inside a standalone function prints garbage (pointer-like digits) instead of the string on native, reproduced in isolation (`t5b_match_only.spl`) with **zero relation to type_params/generics** (oracle prints correctly, native doesn't) | Pre-existing native-path match+text-return bug, out of scope for #158 Phase A; not touched by this patch since none of the 3 changed files touch match/string lowering. Left as-is per task scope; worth a separate bug report. |

Item 4/5 oracle failures and the item-5 native match/text bug are **pre-existing on
commit `0b63b447263`, independent of and unaffected by this 3-file patch** — none
of the touched functions execute unless a function declares its own `<T>...>`.

## Matrix

`sh scripts/check/native-smoke-matrix.shs` run from the worktree
(`/tmp/wt_gen158`, with the patch applied — native-build interprets
`src/compiler/*.spl`, so the gate was live during the run):

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

- **14/15 PASS** — meets the >=14/15 gate.
- Only failure: `option_nil_check` (14) — the single allowed failure per the
  task gate (pre-existing, rc got=1 want=7, fallback_hits=0).
- **0 codegen_fallback_hits** across all 15 cases.
- Notably PASS: `struct_field` (6), `enum_construct` (7), `enum_match` (8),
  `closure_lambda` (12), `result_try_op` (15) — confirming the type-param
  threading and the new fatal-error allowlist entry did not regress any
  non-generic construct.

## Patch

`/home/ormastes/dev/pub/simple/scratchpad/generics_gate.patch` (99 lines, 3
files changed, all within the allowed edit scope).
