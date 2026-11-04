# MIR generic spec cluster (2026-11-04)

Seed (`simple-ref`) runs of `test/01_unit/compiler/50.mir/generic_*_spec.spl`.

| cluster | specs (failed/total) | first error | verdict |
|---|---|---|---|
| A. interpreter wraps `rt_tuple_get<T>() -> T?` in Some | call_arg_inference 2/2, self_method_result_ctor 6/6, then_lambda_slot_coalesce 2/2 | `cannot iterate over this type: Option::Some([Type T])` | product regression, FIXED |
| B. specialization / instance typing asserted after 40.mono deletion | struct_composite_field 15/17, struct_field_instance_paths 3/14, struct_type_param_field 1/7 | `Box.get(` still called; `add` vs `concat`; `E-RTI-003` | specs ahead of erased-generics design (owner decision 2026-10-31, 3b94b409c17); NOT fixed; failing identically at 401883ab000 (11-02) |
| C. removed API | return_owner 2/2 | `mono_caller_return_owner` not found on MirLowering | removed in ab9305d783e (mono pass deletion); spec is stale, owner must delete or rewrite |

Cluster A root cause: PR #5969 (fd65c66254d) changed `rt_tuple_get` to
`rt_tuple_get<T>(..) -> T?` and wrapped it in `_sffi_tuple_get<T>`. Under the
Rust-seed interpreter the `[Type]?` result stays `Some([..])`, so
`parser_type_kind_named_args`/`function_params`/`named_dependencies_into`
iterate an Option. Bisected 401883ab000 (pass) -> fd65c66254d (fail).
Fix: `.unwrap()` (fail-closed; the producers always carry a list, so None is a compiler bug and [] is a legitimate value that must not mask it) at the three `[Type]` sites in
`src/compiler/10.frontend/parser_types_expr.spl`. Scalar/Type sites left as is.

## Resolution of B and C (owner decision 2026-11-04: per-type specialization is obsolete)

- C: `generic_return_owner_spec.spl` and fixture `test/fixtures/bootstrap/generic_return_owner/` deleted (both examples only exercised removed `mono_caller_return_owner`).
- B, `generic_struct_composite_field_spec`: 4 specialization examples rewritten to the erased-body contract (`Box.get` is one shared call with no `Box__get$` copy; `wrap`/`rebox`/`listed` call and define agree on the return type). 10 examples REMAIN FAILING and are real bugs, not obsolete: instance-typed field reads of `[T]`/`T?`/`T` on `Bag<text>`/`Box<text>` lower as integer add instead of string concat, and constructing `Bag(items: [...], first: ...)` reports `mir: enum payload array element type mismatch`.
- B, `generic_struct_field_instance_paths_spec`: 3 failing kept (`array element` and `nested instance: W<W<text>>` lower add instead of concat; `parameter declared without type arguments` no longer refuses `r.v + r.v` on bare `W`). Needs owner call on whether the refusal is still wanted.
- B, `generic_struct_type_param_field_spec`: 1 failing kept (`Pair<text, i64>` operator on a field is no longer refused; same refusal question).
