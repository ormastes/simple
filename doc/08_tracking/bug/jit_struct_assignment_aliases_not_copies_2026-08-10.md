# BUG: JIT struct assignment ALIASES instead of copying (interpreter copies)

- Date: 2026-08-10
- Severity: HIGH (silent cross-engine semantic divergence; corrupts any code
  that assigns a struct and mutates the copy)
- Engines: JIT (bare `bin/simple foo.spl`) WRONG; interpreter
  (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) correct per the
  documented value-type ruling. Binary at measurement:
  `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed).
- Full truth table + probe source:
  `doc/07_guide/language/value_semantics_by_engine.md`

## Repro (minimal)

```
struct Flat:
    a: f64
    b: i64

fn main():
    var f = Flat(a: 1.0, b: 2)
    var f2 = f
    f2.a = 7.0
    print("f.a={f.a}")   # interpreter: 1.0   JIT: 7.0

main()
```

The aliasing is systemic, not assignment-only. Under JIT, mutating a struct
obtained via ANY of these positions mutates the original:

| Position | Interp (copy) | JIT (alias) |
|----------|---------------|-------------|
| `var f2 = f` | orig 1.0 | orig 7.0 |
| copy of struct containing nested struct | orig unchanged | orig changed |
| function argument, callee writes field | orig 1.0 | orig 55.0 |
| returned struct, copy, mutate copy | orig 1.0 | orig 88.0 |
| `var e = lst[0]; e.a = ...` | lst 1.0 | lst 77.0 |
| `var de = d["k"]; de.a = ...` | dict 1.0 | dict 44.0 |

Arrays and text COPY in both engines (verified same run), so this is
struct-specific.

## Secondary divergence (same probe)

`m[1][0] = 9` (nested index assignment) is a semantic error in the
interpreter — `invalid assignment: index assignment requires identifier or
field access as container` — but compiles and works under JIT. One engine
must be wrong; either the interpreter should accept it or the JIT should
reject it.

## Impact

- Any prior measurement of "value semantics" performed with bare
  `simple foo.spl` measured the JIT and concluded ALIAS; measurements via
  the interpreter concluded COPY. Both were faithfully reporting their lane
  (explains the `ca750206e0c7` vs `197b61f972f` contradiction).
- Code written against interpreter semantics (defensive copy-then-mutate)
  silently corrupts originals when run under the default JIT lane.

## Native/AOT lane

NOT MEASURED — two `native-build` attempts of the probe (300s / 550s, second
with `SIMPLE_TIMEOUT_SECONDS=3600`) emitted nothing and produced no binary on
a host saturated by concurrent stage3 builds. The AOT behaviour for struct
assignment is unknown and must be measured separately.

## Expected

If the language intends value semantics for structs (consistent with the
text/array rulings and interpreter behaviour), the JIT must copy structs on
assignment, argument passing, return, and container extraction.
