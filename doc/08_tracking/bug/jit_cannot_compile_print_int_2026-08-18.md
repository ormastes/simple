# JIT cannot compile `print(<int>)` — whole module silently de-JITs

**Status:** OPEN
**Filed:** 2026-08-18
**Found by:** rt_ alias-archaeology probes (binary_runtime_hardening Wave 1).

## Repro (measured 2026-08-18, `bin/simple` = Rust seed at `bin/release/x86_64-unknown-linux-gnu/simple`)

```
# p5.spl
fn main():
    n = 5
    print(n)
```

`SIMPLE_JIT_STRICT=1 bin/simple run p5.spl` →
`Cranelift JIT compile: Module error: codegen: 1 function body/bodies failed to
compile: [main]` and (before the strict fail-open fix of the same date)
interpreter fallback printing `5` with exit 0.

Controls: `print("str")` alone JIT-compiles fine. `print("A n=", n)`
(multi-arg with int) also fails. So the gap is printing a non-text value, not
print itself.

## Impact

Any module printing an integer drops the ENTIRE module to the interpreter
(~100-1000x) with only an `[INFO]` line by default. Because the default
execution mode is interpreter, tests never surface this; it only bites
codegen-lane verification and perf runs — where it invalidates results
(silent-fallback = invalid per the perf verdict rules in
`doc/03_plan/infra/binary_runtime_hardening/plan.md`).

This also blocked the rt_-alias cross-lane parity probe: the codegen-lane
verdict for aliased rt_ externs is unobtainable until this compiles (the alias
itself is exonerated — plain import, aliased import, and direct extern all
failed identically on this print gap; alias-binding gate
`check-import-alias-codegen.shs` PASSes 5/5).

## Taxonomy

SIMPLE-CAPABILITY (JIT lowering gap). Fix in Cranelift lowering for the print
builtin's non-text argument path.
