# Seed JIT silently accepts an unknown field name in named-argument construction

**Status:** OPEN
**Found:** 2026-08-08, while building the positive control for
`interp_static_fn_new_hijacks_named_ctor_2026-07-02` (that bug is RESOLVED; this
is a different defect found by the control)
**Severity:** medium — a typo'd field name compiles and runs with no diagnostic,
and the value lands in the wrong slot rather than being rejected
**Engine:** seed JIT only. Interpreter is CORRECT.

## Symptom

```simple
class Widget:
    id: i64
    size: i64
    static fn new(path: text, size: i64) -> Widget:
        Widget(id: 0, size: size)

fn main():
    val w = Widget(bogus: 3, size: 4)
    print "id={w.id} size={w.size}"
main()
```

| lane | command | result |
|------|---------|--------|
| interpreter | `SIMPLE_EXECUTION_MODE=interpreter bin/simple run r.spl` | `error: semantic: class `Widget` has no field named `bogus`` — CORRECT |
| seed JIT | `bin/simple run r.spl` (default) | `id=3 size=4` — WRONG, no diagnostic |

`bogus` is not a field of `Widget`. The interpreter rejects it. The JIT accepts
it and the `3` still reaches `id`, i.e. the name is discarded and the arguments
appear to bind positionally.

## Why this matters

Named-argument construction (`Point(x: 3, y: 4)`) is the house-style
constructor form per `.claude/rules/language.md`, so this is the common path.
A misspelled or renamed field is silently ignored on the engine that ordinary
programs run on (`bin/simple run` = JIT), while `bin/simple test` runs the
interpreter and would catch it — a classic run/test divergence of the family
already catalogued in `run_vs_test_harness_divergence_2026-07-28.md`.

Because the JIT keeps the positional order, the failure is silent-wrong rather
than merely permissive whenever the mistyped name would have bound to a
different slot than its position implies.

## Not fixed here

The named-argument binder for the JIT lane lives in the Rust seed
(`src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs` is the
interpreter side that gets this right; the JIT lowering path does not consult
it). Rust is bootstrap-only per repo rules, so the fix belongs in the
pure-Simple lowering lane, or in a front-end check that runs before lowering so
both engines inherit it. Recorded rather than guessed.

## Binary identity

`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which prints the
"Rust-built Simple binary is a bootstrap seed only" banner. No pure-Simple
self-hosted binary is deployed on this host, so the self-hosted lane is
untested — the divergence above is seed-JIT vs seed-interpreter.
