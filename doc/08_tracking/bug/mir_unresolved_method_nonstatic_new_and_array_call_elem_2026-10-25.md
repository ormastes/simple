# MIR "unresolved method call" in lint_entry: non-static `fn new`, call-returned struct arrays

- Date: 2026-10-25
- Found by: stage2 `d72188e68ec` native-building `src/app/cli/lint_entry.spl`
  (`C:/dev/wt-rel3-new/build/s3-fwproof/build.log`, rc=1)
- Errors: 269 `unresolved method call` (`new` 182, `with_fix` 38, `slice` 34,
  `with_easy_fix` 5, plus `with_evidence`/`with_evidence_tier`/`with_uncertainty`
  1 each, `is_numeric` 2, `sort_by` 2) and one `indirect callable lacks a proven
  function signature` (a local named `error` shadowing `std.log.error`).

## Root cause per method

| method | route | root cause |
|---|---|---|
| `new` | static-nominal | `impl LintDiag: fn new(..)` and `impl LintRunResult: fn new(..)` have no `static` and no `self`. The core parser (`parse_class_body_method_typed`) synthesizes `self` for every non-`static` impl method, so HIR gives them `SymbolKind.Method`. MIR's static-nominal arm (`method_calls_literals.spl`, the `Unresolved` arm) accepts only a `SymbolKind.Function`, so `LintDiag.new(..)` was rejected. The language guide documents `new` as implicitly static; the pure-Simple parser never implemented that. |
| `with_fix`, `with_easy_fix`, `with_evidence`, `with_evidence_tier`, `with_uncertainty` | runtime-fallback | Cascade: they are chained on `LintDiag.new(..)`, whose result was the const-0 placeholder with no type, so the receiver owner was unknown. They resolve once `new` does (verified, fixture variant A). |
| `slice` | runtime-fallback | `val code_lines = iter_code_lines(src); val cl = code_lines[li]; cl.trimmed.slice(4)`. A local bound from a call returning `[Struct]` -- untyped OR annotated `val xs: [Line] = f()` -- gets no `array_element_struct_syms` row, so the index result is an undecoded word, `cl.raw` loses its declared `text` type, and `slice` (which, unlike `trim`, has no erased-receiver allowance because it is also an array method) has no proven text receiver. Parameters `xs: [Line]` and `val cl: Line = xs[i]` are fine. |
| `is_numeric` | runtime-fallback | `is_numeric` is not a native MIR text builtin (absent from `primitive_text_method_shape`); a typed `text` receiver still fails. Not root-fixed here. |
| `sort_by` | runtime-fallback | `indexed.sort_by(\a, b: ..)` on `[IndexedDuplicateCallReplacement]`. Not root-fixed here. |

Reproduced in ~10 s with the stage2 binary on
`test/fixtures/mir_unresolved_method/{rp,rq}` (single-module and imported
variants); `static fn new` (variant A) and `val cl: Line = lines[i]`
(variant D) each clear their class.

## Compiler fixes (take effect for the next stage built from this source)

1. `src/compiler/10.frontend/core/parser_decls_use.spl`: an impl method named
   `new`, `create`, `default` or `from_*`, with no explicit `self`/`me` param and
   a body whose source never mentions the word `self`, is parsed as static.
   `init` and `with_*` stay excluded (called on instances / builders use self).
2. `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`:
   - `remember_call_hir_return`: an `Array` return also records the element
     owner on the call temp (same fail-closed `optional_payload_struct_name`
     gate as the `Named` arm), so the let-binding copies it.
   - Index lowering: when the base has no element-owner row, recover it from
     the base local's recorded `Array`/`Slice` HIR type (typed lets).

Spec: `test/01_unit/compiler/50.mir/unresolved_static_new_and_call_array_elem_spec.spl`.

## Source workarounds (let the CURRENT stage2 build lint_entry)

Tagged `# WA-MIR-UNRESOLVED-<method>`; remove once a stage built with the fixes
above is the admitted compiler:

- `new`: `static fn new` in `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` (2 sites).
- `slice`: `val cl: CodeLine = ...` and `val body: text = code_lines[li + 1].trimmed` in `src/compiler/35.semantics/lint/_SimdOpportunityLint/{arithmetic_checks,byte_checks,loop_analysis}.spl`.
- `is_numeric`: ASCII digit loop `_wm_all_ascii_digits` in `src/lib/common/ui/wm_chrome_theme.spl`.
- indirect callable: `LintFileErr(error)` binding renamed to `lint_file_error`
  in `entry_and_fixes.spl` (it shadowed `std.log.error`; plain rename, not a WA).

Open (not in this change): `sort_by` on a struct array (`src/compiler/90.tools/fix/rules/impl_/lint_code.spl:156`); `indirect callable lacks a proven function signature` + `undefined variable Future` in `lib.common.target` / `wm_chrome_theme`.
