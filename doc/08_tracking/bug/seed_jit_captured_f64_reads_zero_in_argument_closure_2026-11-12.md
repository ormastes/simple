# Seed JIT: a captured `f64` reads as zero inside a lambda passed as an argument (2026-11-12)

Status: OPEN. Live on `release/1.0.0`; no fallback, no diagnostic. Root cause
not established.

## Repro

```simple
fn run_ff(f: fn(f64) -> f64, v: f64) -> f64:
    f(v)

fn main():
    val k = 0.5
    print "{run_ff(\x: x + k, 2.0)}"      # expect 2.5 -> prints 2.0
```

The same shape through a method (`c.run_f(\x: x + k, 2.0)`) also prints `2.0`.
An `i64` capture is correct (`\x: x + n` with `n = 10` gives 15), and so is a
float capture in a lambda that is called through a local in the same function
(that case currently falls back to the interpreter, so it does not exercise the
JIT capture path).

## What is known

- The lambda's parameter and result are typed `f64` (the callee's declared
  `fn(f64) -> f64`), so this is not the default-parameter-type problem.
- The result is exactly `x + 0.0`, i.e. the capture slot reads as `0.0`, not as
  garbage.

## Not yet done

Dump the `ClosureCreate` capture types and the outlined body's capture load
(`SIMPLE_DUMP_MIR`, `SIMPLE_DUMP_CLIF`) to see whether the f64 is stored raw
and read tagged (or the reverse) in the `RuntimeClosure` capture slot.
