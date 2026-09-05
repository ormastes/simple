# Stage-2 native codegen produces silently wrong values on aarch64

**Status:** OPEN
**Filed:** 2026-09-05
**Host:** aarch64-unknown-linux-gnu (Ubuntu 24.04)
**Severity:** HIGH — four of five defects return a *wrong value with exit 0*, no
diagnostic. A compiler that mis-answers silently cannot be trusted to compile
itself, so these are plausible contributors to the Stage-3 blockage tracked in
`zerokind_is_a_corrupt_aggregate_2026-09-03.md` and
`bin_simple_is_seed_aarch64_stage3_blocked_2026-09-04.md`.

## How reproduced

Compiler under test: `build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple`
(the admitted Stage-2 bootstrap CLI), runtime
`build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-runtime-authority`.

```
cd build/bootstrap/stage2/aarch64-unknown-linux-gnu
SIMPLE_BOOTSTRAP=1 SIMPLE_CACHE_SCOPE=sanity-probe \
SIMPLE_RUNTIME_PATH=<runtime> ./simple native-build \
  --source <repo>/src/app/cli --source <repo>/src/lib \
  --entry-closure --entry <ABS probe.spl> -o <ABS out>
```

Every probe below was cross-checked against the Rust seed
(`bin/simple run <same file>`), which produces the CORRECT answer in all five
cases. The divergence is therefore in Stage-2 **native codegen**, not in the
language definition or the source.

## Defect 1 — a function value passed as a parameter and called returns garbage

Smallest reproducer (9 lines):

```simple
fn apply(f: fn(i64) -> i64, v: i64) -> i64:
    return f(v)

fn dbl(x: i64) -> i64:
    return x * 2

fn main():
    print "direct={dbl(7)}"
    print "indirect={apply(dbl, 7)}"
```

| | stage2 native | seed (`bin/simple run`) |
|---|---|---|
| `direct` | `14` | `14` |
| `indirect` | `1635424192` | `14` |

The garbage value is **not stable across runs** (`2061710912` on an earlier
build of the same source), which is consistent with a live pointer truncated to
32 bits rather than a fixed sentinel. Direct calls are fine; only the
indirect call through a `fn(...)` parameter is wrong.

## Defect 2 — `Array.map` returns an empty array

```simple
fn main():
    val xs = [1, 2, 3]
    val ys = xs.map(_ * 2)
    print "ys_len={ys.len()}"
    print "ys={ys}"
    print "xs={xs}"
```

stage2 native: `ys_len=0`, `ys=` (empty), `xs=[1, 2, 3]`.
seed: `ys_len=3`, `ys=[2, 4, 6]`, `xs=[1, 2, 3]`.

The receiver is intact, so this is the map result construction, not the array.
Very likely the same root cause as defect 1 (the placeholder lambda `_ * 2` is
passed as a callable).

## Defect 3 — calling a closure SEGVs

```simple
fn main():
    val k = 10
    val add_k = \x: x + k
    print "clo={add_k(5)}"
```

stage2 native: **SIGSEGV, rc=139**. seed: `clo=15`.

## Defect 4 — `Dict.len()` returns `-1` (regression of a documented fix)

```simple
fn main():
    var d: {text: i64} = {}
    d["one"] = 1
    print "empty_then_one_len={d.len()}"
    val lit = {"a": 1, "b": 2}
    print "literal_len={lit.len()}"
```

stage2 native: `-1` and `-1`. seed: `1` and `2`.

`CLAUDE.md` § "Native-Codegen Dict Pitfalls" and
`doc/07_guide/language/dict_native_pitfalls.md` both record `Dict.len()`
always-returns-`-1` as **RESOLVED 2026-08-01** and re-verified 2026-08-09. It
is not resolved on this compiler/host. Everything else about Dict is correct
here — `d[k]` reads, `contains_key` (true *and* false), and `keys()` iteration
all give right answers; `.len()` alone is wrong. Whether this is an aarch64
regression or a fix that never reached the Stage-2 lane is not established.

## Defect 5 — a method that does not exist returns a value instead of failing

The same probe called `d.size()`, which is **not a real method**.

- seed: `Runtime error: Function 'Dict.size' not found`, followed by
  `Runtime error: unresolved symbol -- this is a code-generation dispatch gap,
  not a program error. Refusing to substitute a placeholder value`.
- stage2 native: printed `size=3` (the dict has ONE entry), exit 0.

The seed's refusal-to-substitute path is exactly the mitigation described in
`unregistered_extern_silent_nil_2026-08-01.md`. Stage-2 native does not have
it: an unresolved method silently yields a plausible-looking integer. This is
the most dangerous of the five because it makes *typos* into wrong answers.

## What passes (same compiler, same recipe — scope of the damage)

Verified correct on stage2 native: integer arithmetic incl. `/`, `%`, unary
minus and comparison; `while` and `for` loops; string `==` on
same-length-different-content, `!=`, `starts_with` true/false/full-length,
`len()`, concatenation and interpolation (**the `bcmp` stub fix is holding** —
`"abcd" == "abce"` is `false` and `"abcd".starts_with("abd")` is `false`);
struct construction, field readback and field-derived construction; enum
construction and `match` with `case` arms, including payload destructuring
(`Circle(r: 2)` -> 12, `Rect(w: 3, h: 5)` -> 15); `Optional`/nil round-trip
(`== nil`, `??`, `if val` binding); array index, `len()`, `push`, `for`
iteration, and text-element arrays; dict insert, bracket read, `contains_key`,
`keys()` iteration and summation.

## Suggested triage order

Defects 1-3 are one cluster (anything callable that is not a direct static
call). Fixing indirect-call lowering probably fixes all three. Defect 5 is
independent and cheap: port the seed's unresolved-symbol refusal into the
Stage-2 native dispatch path so a missing method traps instead of returning
whatever is in the return register.

## Probes

Sources are throwaway; each is reproduced verbatim above. Each builds in ~6-8s
with the recipe at the top, so re-verification is cheap.
