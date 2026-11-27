# JIT: nested optional/`None`/`Some` pattern holes that remain after the `Ok(None)` fix

Status: open (found by Fable review of c58151f4b5b, 2026-11-27). Identical on seeds `simple-local-20261127r` and `...x`
(x = fix applied). Probes: the review scratch dir `rvb/` (`p1`-`p7`, `q*`); interpret mode answers correctly in every case
below except where noted. Fixed by x and no longer listed: `Result<Ev?>`, `Result<Mode?>`, `Option<Option<i64>>`, loop
statement form (p1, p3, p4, p7, q3_*).

1. ANY/unknown slots (p2). An untyped fn returning `Ok(None)` matched with `case Ok(None)` exhausts under JIT
   (`match expression exhausted`). The fix keys on the slot's static type; an ANY slot has none, so the nested `None` falls to
   the discriminant test, false for raw nil. Needs a runtime test (`rt_is_none`) when the slot type is ANY and no user enum is
   a plausible owner, or return-type inference for the producer.
2. Generic user enum `enum Box<T>: Full(T) / Empty` returning `Box<Ev?>` (p5): `Full(Some(e))` / `Full(None)` arms exhaust, and
   in the reviewer's variant return the `Empty` arm silently. The slot type of `Full`'s payload is the unsubstituted `T`
   (ANY), same root as 1 plus generic-argument substitution in `get_enum_variant_field_types_with_hint`.
3. Unqualified user-enum variants nested (q2_1, q2_4, q6_0, q6_1, p6): `Ok(None)` on `Result<Mode, text>`, `W(None)` on
   `enum Wrap: W(Mode)`, `Ok(Some(x))` on `Result<MyOpt, text>` (user enum with `Some(i64)`/`None`). With a user enum owning the
   variant the nested bare `None`/`Some(x)` should resolve to that enum's variant (interpret does); JIT exhausts. The
   name-based path `is_real_enum_variant_name` + `enum_runtime_id_for_pattern` returns id 0 when more than one enum owns
   the name, so the discriminant test is skipped or mismatched.
4. Qualified `Ok(MyOpt.Some(x))` (p6c) binds a garbage payload under JIT (r: 2304317179681, x: 3958349352129; interpret: 5).
   The binder reads the payload slot as the `Some` dual-representation form (`payload_slot_expr`, `rt_enum_id == OPTION_ENUM_ID`
   guard) although the enum is a user enum, so it skips the payload unwrap. Fix direction: pass the owning enum into
   `payload_slot_expr` and apply the raw-form guard only for the builtin Option.

Regression test home when fixed: `compiler/tests/jit_nested_option_result_user_none_enum_match.rs`.
