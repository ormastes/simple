# MIR lane 1 (provider/struct specs) stale specs - 2026-11-04

All eight listed 50.mir specs are green; every fix is a spec-side update, no product change.

| spec | class | root cause | fix |
|---|---|---|---|
| provider_layout_demand | b | staged non-fatal `non-exhaustive enum match` warning (545ac887b09) lands in `errors`, spec asserted "no MIR line" | filter that warning (same precedent as bare_variant_retained_subject_spec) |
| provider_method_scope_retirement | b | `MirSignature.params_known` is the extern-declaration arity flag (mir_types.spl:63, 9d6f087fab5); defined functions never set it | assert `params_known or params.len() > 0` (predicate of mir_verify.spl:580) |
| missing_struct_field_lowering | b | message reworded by 3fea4ceba33 to `field 'x' is absent from exact (value\|struct/class) layout 'M::T'` | match new wording |
| struct_inequality_lowering | b | records without `__eq__` are now structural (90d1f293648); diagnostic only remains when structural eq is unsupported | negative case uses a trait-object field |
| residual_operator_placeholder_method | b | spec fixture string `"<{x * self.scale}>"` interpolated in the spec itself (`variable x not found`) | escape braces `{{ }}` |
| array_move_lowering (2) | b | untyped lambda called indirectly fails closed (`lacks a proven function signature`); `Any` slot is rejected in safe code | typed `val f: fn(i64) -> i64`; `Any` slot -> erased generic `Dyn<T>` slot |
| provider_method_demand_determinism, static_generic_factory_typeparam | - | already green | none |

Possibly dead code: `function_lowering.spl` `no field '..' on '..'` (line ~2095) is now unreachable
when `layout_owner` is set, since the qualified tier returns the "absent from exact" error first.
