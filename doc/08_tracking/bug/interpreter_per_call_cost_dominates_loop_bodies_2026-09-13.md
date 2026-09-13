# Every loop-body shape above the generic floor is dominated by one call

- Status: OPEN (2026-09-13)
- Found by: PERF-6, base `origin/main` f26970e9d93, seed sha256 `22878382bc1b5ccf...`

## The corpus

12 statement shapes that dominate real stdlib loops, timed in-loop at
n = 2,000,000 under `SIMPLE_EXECUTION_MODE=interpreter`, best of three:

| shape | ns/iteration | src/lib/common sites |
|---|---:|---:|
| range `for` (`acc = acc + i`) | 96 | 39 |
| nested `for` (inner 2 stmts) | 264 | -- |
| array index read in a `for` | 1,190 | 10,859 |
| array `push` in a `for` | 1,184 | 5,774 |
| text concat | 1,049 | 1,843 |
| dict get + set | 1,456 | 721 |
| `while` with two accumulators | 1,587 | 4,111 |
| closure call | 2,199 | -- |
| method call on a class (`me` mutator) | 3,079 | 21,601 |
| `match` on an enum (+ a `pick()` call) | 4,647 | 953 |
| Option unwrap `f(i) ?? 0` | 4,982 | 167 |
| StringBuilder `push` | 7,905 | 54 |
| tuple destructure `val (a, b) = pair(i)` | 8,733 | ~0 |

## The finding

The three cheapest generic shapes -- array index read, array push, text concat
-- all sit at 1,050-1,190 ns/iteration for a two-statement body. **That is the
generic walk's floor, not a property of arrays or of text.** Arrays, dicts and
text concatenation are not distinct hot mechanisms; PERF-1 already certified
this space linear.

Everything above the floor is a *call*: the excess is ~1,000 ns for a closure,
~1,900 ns for a class method, ~3,500-3,900 ns when the shape also calls a
helper (enum match, Option unwrap). By cost x frequency the largest single
target in the interpreter is therefore **the per-call cost of a method on a
class or struct**: 3,079 ns x 21,601 sites.

`src/compiler_rust/compiler/src/interpreter_call/` carries 282 `.clone()` /
`Env::clone` sites. PERF-6 did not attempt this: it is not a contained edit, and
on this host it cannot be measured honestly without a CPU-time harness (see
`perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13.md`). Filed so the
next lane starts from the measurement rather than from a guess.

## Separately anomalous

`val (a, b) = pair(i)` costs **8,733 ns/iteration**. A call plus a two-name
tuple bind should be ~4,000 given the closure and method-call rows above; the
extra ~4,500 ns is unexplained and is the largest per-statement cost in the
corpus. The destructuring path is also the only block-shadow capture path that
still allocates a scratch vector.
