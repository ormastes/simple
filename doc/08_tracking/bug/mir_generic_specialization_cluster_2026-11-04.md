# MIR generic spec cluster (2026-11-04)

Seed (`simple-ref`) runs of `test/01_unit/compiler/50.mir/generic_*_spec.spl`.

| cluster | specs (failed/total) | first error | verdict |
|---|---|---|---|
| A. interpreter wraps `rt_tuple_get<T>() -> T?` in Some | call_arg_inference 2/2, self_method_result_ctor 6/6, then_lambda_slot_coalesce 2/2 | `cannot iterate over this type: Option::Some([Type T])` | product regression, FIXED |
| B. specialization / instance typing asserted after 40.mono deletion | struct_composite_field 15/17, struct_field_instance_paths 3/14, struct_type_param_field 1/7 | `Box.get(` still called; `add` vs `concat`; `E-RTI-003` | specs ahead of erased-generics design (owner decision 2026-10-31, 3b94b409c17); mono-era names rewritten (Resolution below); the instance-typing failures FIXED 2026-11-04 (Cluster B section below) |
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
- B, `generic_struct_composite_field_spec`: 4 specialization examples rewritten to the erased-body contract (`Box.get` is one shared call with no `Box__get$` copy; `wrap`/`rebox`/`listed` call and define agree on the return type). The other 10 examples were real bugs, not obsolete (instance-typed field reads of `[T]`/`T?`/`T` on `Bag<text>`/`Box<text>` lowered as integer add instead of string concat; constructing `Bag(items: [...], first: ...)` reported `mir: enum payload array element type mismatch`): 9 fixed by this lane (section below); 1 open (`boxit("t")`, a generic CALL result carrying `Box<text>` to a field read).
- B, `generic_struct_field_instance_paths_spec`: the 3 failing (`array element`, `nested instance: W<W<text>>`, `parameter declared without type arguments`) fixed by this lane; the refusal on bare `W` is restored (section below).
- B, `generic_struct_type_param_field_spec`: the 1 failing (`Pair<text, i64>` operator on a field) fixed by this lane: the refusal was stale since H-ANNOT, the example now pins the integer add (section below).

## Cluster B, the real-bug part: instance typing of container fields (2026-11-04, lane work/mir-generic-text-concat)

Not every B failure is a mono-era assertion. Under erasure the USE SITE
knows the instance (`b: Bag<text>`, `Bag(items: ["a"], first: "a")`), and
three things lost it between the declaration and a `+`:

1. **Construct site refused** `Bag(items: ["a", "b"], first: "a")` with
   `mir: enum payload array element type mismatch`.
   `lower_struct_array_initializer_v1` (`switch_operators_calls.spl`) fed
   the template's `[T]` as the literal's declared context, so
   `enum_payload_local_compatible(T, "a")` fell to its `case _: false`.
   Fix: a declared element type that mentions a type parameter is no
   context (plain `lower_expr`; the literal's own elements type the array).
2. **Field read of `items: [T]` / `first: T?` lowered as the template.**
   `expr_dispatch.spl` Field arm: an over-param field only resolved from a
   fully instantiated stamp on the read; the parameter / annotated-let /
   call-result route (base HIR `Bag<text>`) and the construct route had no
   substitution, so `field_type = lower_type([T])` = `[i64]`, the Index
   read decoded i64, and `+` was an integer add. Fix:
   `generic_instance_field_substituted` substitutes the base local's HIR
   type arguments into the declared field type (both parameter spellings,
   through Array/Slice/Optional/Dict/Result/Tuple/Named) and feeds the
   existing `instance_field_mir_type` / `mark_instance_field_local` path;
   `option_inner_hir_type_for_local` (`method_calls_literals.spl`) no
   longer lets a declared `T?` outrank the field local's remembered
   `text?` for `??`.
3. **Construct results remembered an argumentless `Bag`.** The construct
   site recorded `Named(Bag, [])`, so route 2 had nothing to substitute
   from. Fix: `bind_struct_type_params` binds each parameter from the
   stored value's HIR type (`v: T` vs `text`, `items: [T]` vs `[text]`,
   a present `T?` from the bare payload; a text value from its MIR word,
   a scalar only when the source is a scalar LITERAL -- an erased generic
   call result `ident("a")` is an i64 word too and must not bind T=i64,
   pinned by instance_paths "an erased generic call result does not
   guess the instance") and the result remembers `Bag<text>` only when
   every parameter bound. This also carries `W<text>` into
   `[W(..), W(..)]` (the Index arm now keeps a `Named` element's
   arguments on the decoded element) and `W<W<text>>`. Not substitution
   inside a generic body: `Bag<T>` substitutes to itself and stays
   unknown, as before.

Refusal verdicts (spec (3) of the lane):

- `generic_struct_type_param_field` "parameter declared `Pair<text, i64>`
  ... an operator on it is refused": **stale**. The example's own comment
  conditions the refusal on the frontend dropping annotation arguments;
  1f20215b28d (H-ANNOT, 2026-10-12) made same-module annotations retain
  them and rewrote the equivalent `generic_struct_field_instance_paths`
  examples from `refused` to `concat`/`add`, but never touched this spec.
  `p.b + 1` on a known `Pair<text, i64>` is the integer add it emits today;
  the example now pins that (`expect_clean` + `add nsw i64`, no concat).
- `generic_struct_field_instance_paths` "parameter declared without type
  arguments" (`r: W`, `r.v + r.v`): **regressed, restored.** The refusal
  was lost as a side effect of 3b94b409c17: a `T` slot lowers to the
  erased i64 word instead of a struct named `T`, so the Field arm's
  unknown-instance note (`struct_value_syms[field] = "T"`) no longer made
  the operand a struct and `+` became a raw `add nsw i64` of two erased
  words with no diagnostic -- which the erasure contract itself calls a
  gap to report, not guess (`decode_erased_binop_operands`). Restored in
  `binary_struct_owner`: a declared `TypeParam` operand whose note names
  that same parameter is the unknown-instance read, so the existing
  "operator overload for struct T" refusal fires. Inside an erased generic
  body `x.v` on `x: W<T>` resolves to `T` (known, erased) and is untouched.

Before -> after (seed `simple-ref`, one spec per process):

| spec | before | after | still failing |
|---|---|---|---|
| generic_struct_composite_field | 7/17 (origin, mono examples already rewritten) | 16/17 | 1 real, open: `boxit("t")` generic CALL result carrying `Box<text>` to a field read (call-site argument binding, not field typing) |
| generic_struct_field_instance_paths | 11/14 | 15/15 (one example added) | -- |
| generic_struct_type_param_field | 6/7 | 7/7 | -- |

Regression set (16 rc=0 `50.mir` generic/struct/operator/concat/any specs,
incl. `any_binop_boxed_result`, `any_index_read`): all pass before and
after; no pass -> fail.
