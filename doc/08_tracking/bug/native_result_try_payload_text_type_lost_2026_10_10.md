# Native MIR loses the declared text type across `Result?`

## Evidence

The native producer `aa404c21c4d2435e871ac0f57903da18610b452323fe09355f86b9cdddb0a41f` failed object generation for `src/app/bug/workaround_store.spl` with 19 unique MIR errors, including unresolved `trim` at lines 91, 170, and 178 and unresolved `index_of` at line 94. The captured failure is `/dev/shm/simple-phase3-1000-object-attempt-20261010/continuation-02/row-0001/failure-details.json`; no retry is represented here.

`workaround_host_read` and `workaround_git` return `Result<text, text>`. In MIR `lower_try_expr`, the `Result` success payload is read with `rt_enum_payload` as an `i64`, then passed directly to `enum_payload_value`. The `Result` branch does not retain the declared `ok_type` on that payload local. Consequently text-special method dispatch has no receiver `Str` type or text-local provenance, even though its builtin table maps `trim` to `rt_string_trim`.

The shared `decode_declared_enum_payload_slot` already decodes declared payload kinds and records their HIR type. Enum-pattern text payload handling separately confirms that the Result enum slot is an erased word and must be converted through `rt_interp_cstr` before native string operations.

## Repair and temporary workaround

The compiler repair routes `Result?` success payloads through `decode_declared_enum_payload_slot`, preserving the declared type and existing payload-class rules rather than relabeling the raw MIR word as a fat pointer.

Until a rebuilt producer contains that repair, `workaround_store.spl` explicitly annotates four `?`-extracted text locals. The `@workaround` tags name this report. These annotations retain the source contract that `?` yields `text`; they do not change validation behavior.

## Regression coverage

The companion native fixtures cover unannotated Result text with UTF-8/whitespace/empty trimming, an explicitly typed control, custom `trim` precedence, nontext rejection, and wrong-arity rejection. They are pending execution; no native/compiler result is claimed.


## Resolved 2026-10-31

Root cause: `lower_try_expr`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, Result
branch) read the Ok payload with `rt_enum_payload` as a raw `i64` and never
restored the declared `ok_type`, so text methods (`trim`, `index_of`) were
unresolved and concatenation stringified the handle.

Fix (already on release/1.0.0 before this resolution; no new compiler change):
`265252279c9` routes the static Result payload through
`decode_declared_enum_payload_slot`; its `Str` arm
(`src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`) restores
text via `option_text_value` (`rt_interp_cstr`) with `bootstrap_text_type`.
`3aa79ca1610` applies the same decoder when the static base type is unknown but
the lowered call remembered its declared Result return. Type aliases need no
MIR handling: HIR expands `type R = Result<text, E>` to the underlying shape
(`src/compiler/20.hir/hir_lowering/type_aliases.spl`).

Test: `test/01_unit/compiler/mir/result_try_text_payload_spec.spl`, three
examples:
1. single module, direct and `type`-aliased `Result<text, text>` callees;
2. three modules lowered through `module_surfaces_from_modules` +
   `hirlowering_for_module` + `MirLowering.lower_module(consumer, providers)`:
   `lib.io.ops` defines `read_bounded`, `lib.host` does
   `export use lib.io.ops.{read_bounded as host_read}`, `app.main` imports
   `host_read` and does `host_read(path, 16)?.trim()` - the
   `workaround_host_read` / `secure_temp_dir` re-export shape;
3. interpreter execution of the same text semantics and Err propagation.
MIR examples assert zero MIR errors, one `rt_string_trim`, no
`rt_raw_i64_to_string`, and that every `rt_enum_payload` destination is an
argument of an `rt_interp_cstr` call.

Sensitivity, run on 2026-10-31 with the Rust seed
(`/Users/ormastes/simple/bin/simple test <spec>`, interpreter) by temporarily
editing the worktree source and restoring it afterwards:
- replacing `value = self.option_text_value(raw, self.bootstrap_text_type())`
  in the decoder `Str` arm with `pass`: examples 1 and 2 FAIL, 3 passes;
- replacing the static-path `case _: return self.decode_declared_enum_payload_slot(pl, ok_type)`
  with `case _: return pl`: examples 1 and 2 FAIL, 3 passes;
- disabling the remembered-call fallback (`find_local_hir_type(res_local.id)`
  branch): all pass, so the re-export alias is resolved by the static
  `enum_match_expr_type` path, not by `resolved_call_hir_return_type`.
Unmodified source: 3/3 pass.

Workarounds removed: all `val ...: text = ...?` annotations in
`src/app/bug/workaround_store.spl` (`content`, `wal`, `final_head`, `head`) and
the three `@workaround bug=native_result_try_payload_text_type_lost_2026_10_10`
tags.

Not verified here: native execution of the fixture or of `workaround_store`
with a freshly built stage2 producer (only the Rust seed was available; its JIT
falls back to the interpreter). The MIR spec runs the Simple compiler's own
lowering in the interpreter; the real driver's module-surface construction may
differ from `module_surfaces_from_modules`.
