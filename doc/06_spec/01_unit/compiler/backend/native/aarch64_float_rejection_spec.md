# AArch64 direct backend scalar floating-point rejection

Requirement: REQ-AARCH64-FLOAT-REJECT-001.
Executable source: test/01_unit/compiler/backend/native/aarch64_float_rejection_spec.spl.
Five scenarios, zero placeholders.

| Scenario | Fixture | Expected result |
|---|---|---|
| Integer control | i64 constant function | accepted by `isel_module_aarch64`, one MachFunction produced |
| Float return type | f64 return signature | one diagnostic naming the function and the floating-point return type |
| Float parameter type | f64 parameter signature | one diagnostic naming the function and the floating-point parameter type |
| Float local type | f32 temp local | one diagnostic naming the function and local 1 |
| Float constant | `MirConstValue.Float(1.5)` const instruction | one diagnostic naming the function and the floating-point constant |

Each scenario builds a real `MirModule` and calls `a64_module_float_rejections`
(the module-level scan that `isel_module_aarch64` runs before lowering).
`isel_module_aarch64` panics with the first diagnostic when the scan is
non-empty, and `a64_lower_const` panics on any operand-carried float constant
that bypasses the scan. Integer-only programs are unaffected.

This is the repair for bug
`native_aarch64_scalar_float_silent_integer_lowering_2026_11_03`: the direct
backend lowers every scalar binop as an integer op and used to lower float
constants as zero; it now fails explicitly until scalar FP registers, ABI and
instruction encodings exist. No floating-point support is implemented and no
LLVM-lane behavior changes.

Reproduce with the admitted self-hosted runtime once deployed:

```bash
bin/simple test test/01_unit/compiler/backend/native/aarch64_float_rejection_spec.spl --mode=interpreter
```

Current-session evidence (Rust seed interpreter, aarch64 Linux host):
`outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0`.
