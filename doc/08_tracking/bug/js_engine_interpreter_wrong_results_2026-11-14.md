# In-tree JS interpreter returns wrong values and can end the process silently (2026-11-14)

Status: OPEN. Severity: medium for the module, low for the product — nothing
in `src/` imports `browser_engine/js/interpreter.spl` or `js/parser.spl`
(`grep -rl "browser_engine.js.interpreter" src` lists only the file itself).

## Repro (seed built 2026-11-14 09:32, interpreter lane)

```
use std.gc_async_mut.gpu.browser_engine.js.interpreter.{JsInterp}
use std.gc_async_mut.gpu.browser_engine.js.values.{js_to_string}
fn main():
    var it = JsInterp.new()
    it.eval_source("var x = 5; x = x + 1;")
    print "Q1 " + js_to_string(it.get_var("x"))
    var it2 = JsInterp.new()
    print "Q2 start"
    it2.eval_source("function add(a, b) {{ return a + b; }} var r = add(2, 3);")
    print "Q2 " + js_to_string(it2.get_var("r"))
```

| program | expected (ECMAScript) | actual |
|---|---|---|
| `var x = 5; x = x + 1;` then `x` | `6` | `1.0` |
| `var r = 5; r -= 2; r *= 4;` | `12` | `-8.0` |
| `var r = 7; r++; r--; ++r;` | `8` | `1.0` |
| `var r = 'x'; r += 'y';` | `xy` | `0.0` |
| `var r = 1; r = r << 3;` | `8` | `0.0` |
| `switch (2) { case 1: … case 2: r = 20; break; default: r = 30; }` | `20` | `30.0` |
| `if (1 > 2) { r = 'a'; } else { r = 'b'; }` | `b` | `undefined` |
| `'a' + 1` | `a1` | `a1.0` |
| any program that calls a function, uses `for`, an object literal, an array literal, `?:`, `let`/`const`, `==`/`===` | a value | **the host process stops after `eval_source` with exit code 0 and no message** (`Q2 start` is the last line printed) |

Also in `js/values.spl`: `js_to_number(Str(_))` returns `0.0` for every string
(lines 240-244, both branches), and `js_to_string(Num(7.0))` is `7.0`, not `7`.

The silent exit-0 is the more serious half: a spec whose body does this
executes nothing afterwards and still exits 0.

## Consequence for coverage

`js/parser.spl` (360 executable lines) and `js/interpreter.spl` (258) are
"never loaded" in `doc/10_metrics/gpu/render_coverage_2026-11-14.md`. They
cannot be brought to 90% with behavioural specs until the interpreter is
correct; assertions written today would either fail or pin wrong values.

## Decision needed

Delete `browser_engine/js/{lexer,parser,ast,interpreter,dom_bridge}.spl` as
unused, or repair them and wire a consumer. `js/values.spl` is covered by
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/js_values_heap_spec.spl`
for the parts that are correct.
