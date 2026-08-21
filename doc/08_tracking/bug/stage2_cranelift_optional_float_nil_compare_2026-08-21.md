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
