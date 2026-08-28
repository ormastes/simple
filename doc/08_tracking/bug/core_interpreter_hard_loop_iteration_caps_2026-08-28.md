# Core interpreter: hard iteration caps on `while` (1,000,000, errors) and range `for` (1,000,001, SILENT stop)

**Date:** 2026-08-28  **Status:** OPEN  **Area:** `src/compiler/10.frontend/core/interpreter/eval.spl`
**Found by:** perf_interp profiling lane (release/2026-08-27 tip `bb87306b64c`)

## Defect

- `eval.spl:810` `eval_while_expr`: `val max_iterations: i64 = 1000000`; on reaching it the loop
  stops and `eval_set_error("while loop exceeded maximum iterations")` fires. A legitimate
  `while i < 2_000_000` program is a runtime ERROR.
- `eval.spl:741` `eval_for_expr` (range form): `while _range_iter < 1000001:` — the loop simply
  ends after 1,000,001 iterations with NO error, so `for i in 0..2_000_000: acc += i` returns a
  wrong result silently.

Both caps are unconditional (no env/flag), and they differ from each other and from the Rust
seed (no cap). A 1M-step loop is ~1 s of work in an interpreter; this is a feature limit that
will surface as a wrong answer, not a diagnostic, in the `for` case.

## Reproduce (once a pure-Simple binary can drive `core_interpret`)

```
fn main() -> i64:
    var acc: i64 = 0
    for i in 0..1500000:
        acc = acc + 1
    print "{acc}"     # core interpreter prints 1000001, expected 1500000
    0
```

## Fix direction

Make the cap opt-in (an execution-limit knob such as the existing `--execution-limit` CLI option
in `src/app/run/main.spl:124`), and make the range-`for` path report an error like `while` does
instead of truncating silently. Not changed in the perf lane (feature-affecting).
