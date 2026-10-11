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
