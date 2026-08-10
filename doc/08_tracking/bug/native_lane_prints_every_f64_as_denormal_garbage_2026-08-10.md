# The native lane prints EVERY f64 as denormal garbage, not just computed ones

- **Date:** 2026-08-10
- **Status:** OPEN
- **Lane:** native only (`native-build`). Interpreter and JIT are correct.
- **Class:** silent wrong-value, total for the type.

## Symptom

```
fn main():
    val b: f64 = 16.0
    val c: f64 = b.sqrt()
    print c
    print b
```

```
SIMPLE_NATIVE_BUILD_RUST=1 simple native-build --source natsrc \
    --entry natsrc/nat2.spl -o n2 && ./n2
0.0000000000000000000000000000000000000000000000000000000000...
0.0000000000000000000000000000000000000000000000000000000000...
```

Both lines are denormal garbage — **including `print b`**, which is a plain
typed float local holding a literal `16.0`. No method call, no computation, no
argument-position subtlety. The native lane cannot render any `f64`.

The magnitude (~1e-313) is what an `i64` looks like when its bit pattern is
reinterpreted as a double, so the value is reaching the formatter as an integer
word and being bit-cast rather than converted — the mirror image of the
interpreter/JIT defect in
`float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`,
where a float word was read as an integer.

## Why this is filed separately, and how it was isolated

Found while verifying the argument-position fix across lanes. The tempting
reading was that the fix regressed native: before the fix native printed
`577023702256844800` (the tagged bits) for `print b.sqrt()`, and after it
printed this garbage instead. The control above rules that out — `print b` on a
**literal-initialised** float is equally broken, identically, on a binary built
from unmodified `bb43fac0cf5` and on the fixed one. The lane was already unable
to print floats; the fix only changed which wrong thing it prints, by making the
value take the (broken) float rendering path instead of the integer one.

Note the default pure-Simple `native-build` refuses to run from a bare seed
("pure-Simple tool 'native-build' unavailable; refusing Rust fallback"), so this
was measured through the Rust `native_project` pipeline via
`SIMPLE_NATIVE_BUILD_RUST=1`. Whether the pure-Simple native path shares the
defect is UNMEASURED.

## Not yet investigated

Likely candidates are the native runtime's `rt_raw_f64_to_string`
(`src/runtime/runtime_native.c`) and the native print lowering's choice between
the raw-f64 and tagged-value entry points. Not confirmed — this filing records
the measurement, not a root cause.

## Related

- `doc/08_tracking/bug/float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
- `doc/08_tracking/bug/f64_integral_to_text_drops_fraction_2026-07-25.md`
