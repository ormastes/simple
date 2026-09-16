# Stage 2 Cranelift mislowers optional-float nil comparison

While compiling the real ARM64 SimpleOS desktop closure, Stage 2 lowered the
`f64? != nil` checks in `parse_pct_value` to `icmp_imm.f32`. Cranelift rejected
both instructions because integer comparison cannot control an `f32` value.

Optional pattern binding triggers the same bad lowering, so this cannot be
worked around honestly in the parser: parsing can fail and the value must stay
optional until a valid nil/tag check succeeds. Fix the compiler so explicit
optional-float equality/inequality and pattern binding inspect the optional
representation rather than emitting float `icmp_imm`; then unwrap only on the
non-nil branch.

## 2026-08-22 pure-Simple owner repair

`hir_expr_is_optional_type` now recognizes the payload-bearing `Optional`
variant by enum discriminant before any payload match, mirroring the existing
staged-self-host safeguard in `MirLowering.lower_type`. Consequently both
operand orders of `== nil` and `!= nil` route through `rt_is_none` or
`rt_is_some` for `f32?` and `f64?`. Cranelift comparison selection now consults
both operand types, and a genuine bare float condition is explicitly converted
to Bool with `fcmp ne 0.0` before `brif` can perform its integer-zero test.

Focused coverage lives in
`test/01_unit/compiler/mir/optional_float_nil_compare_lowering_spec.spl`.
The one permitted check with admitted pure-Simple Stage 2 SHA-256
`aea4cbf8ed9e88cd68fc844e4e645b83ddba4659dd6c2cfa45588b51c2c58821`
failed closed before loading the spec because that diagnostic compiler exposes
no `test` command (`error: unknown command 'test'`). No Rust seed, stub fallback,
shared cache, or second verification attempt was used; executable confirmation
therefore remains pending an admitted test-capable self-host.
