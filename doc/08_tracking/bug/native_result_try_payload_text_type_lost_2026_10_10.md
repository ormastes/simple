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

Test: `test/01_unit/compiler/mir/result_try_text_payload_spec.spl` lowers a
direct and an aliased `Result<text, text>` callee through HIR/MIR and asserts
zero MIR errors, one `rt_string_trim` dispatch, no `rt_raw_i64_to_string`, and
that every `rt_enum_payload` word feeds `rt_interp_cstr`; it also executes the
same shapes in the interpreter (text equality, length, Err propagation). It is
red with the decoder `Str` arm disabled and green with it.

Workarounds removed: the tagged `val ...: text = ...?` annotations in
`src/app/bug/workaround_store.spl` (`load_workarounds_at`,
`workaround_bug_snapshot`, `workaround_refresh_locked`).

Not verified here: native execution of the fixture or of `workaround_store`
with a freshly built stage2 producer (only the Rust seed was available; its
JIT falls back to the interpreter). The 2026-10-30 native receipts above remain
the native evidence.
