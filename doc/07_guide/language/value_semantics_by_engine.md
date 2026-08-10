# Value vs Alias Semantics, Per Engine (measured 2026-08-10)

**Settles the contradiction between "structs/arrays/text are value types" and
the `ca750206e0c7` probe showing `var f2 = f; f2.a = 7.0` mutating `f`.**
Both observations were real. The discriminator is **(kind, engine)**:

> **Arrays and text copy on assignment in every engine.
> Structs copy in the interpreter but ALIAS in the JIT** — on plain
> assignment, argument passing, return, and container extraction alike.

## Probe

`print`-based standalone probe (no assertions), run from the repo root with
relative paths; CONTROL line printed 42 in every run. Binary:
`bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, self-identified via
its bootstrap-seed banner). Probe source is reproduced at the bottom.

- Interpreter lane: `SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl`
- JIT lane: bare `bin/simple probe.spl`
- Native/AOT lane: `bin/simple native-build probe.spl` (see status below)

## Truth table (actual printed values)

`Flat{a: f64, b: i64}`, `Outer{inner: Flat}`. "orig" is the value observed on
the ORIGINAL binding after mutating the copy/callee/extracted value.

| # | Case | Interpreter | JIT | Verdict |
|---|------|-------------|-----|---------|
| S1 | `var f2 = f; f2.a = 7.0` | `f.a=1.0 f2.a=7.0` | `f.a=7.0 f2.a=7.0` | interp COPY, **JIT ALIAS** |
| S2 | `o.inner.a = 99.0` (write through nested field) | `99.0` | `99.0` | persists in both (expected) |
| S2b | `var o2 = o; o2.inner.a = 33.0` | `o.inner.a=99.0 o2=33.0` | `o.inner.a=33.0 o2=33.0` | interp COPY, **JIT ALIAS** |
| S3 | pass struct as arg, callee sets `.a=55.0` | `g.a=1.0` | `g.a=55.0` | interp COPY, **JIT ALIAS** |
| S4 | struct returned from fn, copy, mutate copy | `r.a=1.0 r2.a=88.0` | `r.a=88.0 r2.a=88.0` | interp COPY, **JIT ALIAS** |
| S5 | `var e = lst[0]; e.a = 77.0` | `lst[0].a=1.0 e.a=77.0` | `lst[0].a=77.0` | interp COPY, **JIT ALIAS** |
| S5b | `lst[0].a = 66.0` (write through index) | `66.0` | `66.0` | persists in both |
| S6 | `var de = d["k"]; de.a = 44.0` | `d["k"].a=1.0 de.a=44.0` | `d["k"].a=44.0` | interp COPY, **JIT ALIAS** |
| A1 | `var a2 = a1; a2[0] = 100` | `a1[0]=1 a2[0]=100` | `a1[0]=1 a2[0]=100` | COPY in both |
| A2 | `var row = m[0]; row[1] = 5` | `m[0][1]=0 row[1]=5` | `m[0][1]=0 row[1]=5` | COPY in both — copy-out LOSES writes |
| A2b | `m[1][0] = 9` (nested index write) | **semantic error**: "index assignment requires identifier or field access as container" | `m[1][0]=9` works | **engine divergence in accepted syntax** |
| T1 | `var t2 = t1; t2 = t2 + "X"` | `t1=abc t2=abcX` | `t1=abc t2=abcX` | COPY/value in both |

## Why the prior "contradiction" happened

- The copy-semantics bugs (`levenshtein_distance` DP rows lost, commit
  `197b61f972f`; array-of-array copy-out) were **array** cases — arrays copy
  in every engine, so copy-out-write-no-write-back genuinely loses writes.
- The `ca750206e0c7` probe was a **struct** case run under the default lane
  (bare `simple foo.spl` = JIT), where structs alias. Nested
  `o.inner.a = 99.0` persisting is not evidence either way — a write through
  a field path persists under both semantics (S2 shows both engines agree).
- Dict-of-dict "propagation" reports are consistent with dicts being
  reference-backed containers in at least some lanes; the safe rule remains:
  **never rely on copy-out-mutate for any container — write back through the
  full index/field path** (`m[i][j] = v` style), which persists everywhere
  the syntax is accepted.

## Practical rules for code that must run on multiple engines

1. Never mutate a struct obtained by plain assignment, argument, return, or
   container extraction and expect a *specific* effect on the original —
   the effect differs by engine. Treat such values as read-only; rebuild and
   reassign instead.
2. For arrays: always write through the original binding
   (`m[i] = row` write-back, or direct `lst[i].f = v` / `m[i][j] = v` where
   the interpreter accepts it). Note A2b: nested index assignment does not
   parse in the interpreter lane — write back the row instead.
3. Text is a value type everywhere (matches the existing ruling).

## Defect status

If the language intends value semantics (the interpreter's behaviour, and the
documented ruling for text/arrays), then **the JIT aliasing of structs in six
distinct positions (S1, S2b, S3, S4, S5, S6) is a correctness defect**, filed
as `doc/08_tracking/bug/jit_struct_assignment_aliases_not_copies_2026-08-10.md`.
The interpreter's rejection of `m[1][0] = 9` is a second, smaller divergence
(same bug doc).

Native/AOT (`native-build`) status: **NOT REACHED**. Two build attempts of the
probe (`bin/simple native-build tmp_probe/probe.spl`, 300s and 550s wall,
second with `SIMPLE_TIMEOUT_SECONDS=3600`) produced no output lines and no
binary before termination, on a host saturated by concurrent stage3
native-builds. The AOT column of the truth table is unmeasured — do not infer
it from either other engine.

## Probe source

```
struct Flat:
    a: f64
    b: i64

struct Outer:
    inner: Flat

fn mut_arg(s: Flat):
    s.a = 55.0

fn make_flat() -> Flat:
    return Flat(a: 1.0, b: 2)

fn main():
    print("CONTROL={40 + 2}")
    var f = Flat(a: 1.0, b: 2)
    var f2 = f
    f2.a = 7.0
    print("S1 f.a={f.a} f2.a={f2.a}")
    var o = Outer(inner: Flat(a: 1.0, b: 2))
    o.inner.a = 99.0
    print("S2 o.inner.a={o.inner.a}")
    var o2 = o
    o2.inner.a = 33.0
    print("S2b o.inner.a={o.inner.a} o2.inner.a={o2.inner.a}")
    var g = Flat(a: 1.0, b: 2)
    mut_arg(g)
    print("S3 g.a={g.a}")
    var r = make_flat()
    var r2 = r
    r2.a = 88.0
    print("S4 r.a={r.a} r2.a={r2.a}")
    var lst = [Flat(a: 1.0, b: 2)]
    var e = lst[0]
    e.a = 77.0
    print("S5 lst0.a={lst[0].a} e.a={e.a}")
    lst[0].a = 66.0
    print("S5b lst0.a={lst[0].a}")
    var d = {"k": Flat(a: 1.0, b: 2)}
    var de = d["k"]
    de.a = 44.0
    print("S6 dk.a={d[\"k\"].a} de.a={de.a}")
    var a1 = [1, 2, 3]
    var a2 = a1
    a2[0] = 100
    print("A1 a1_0={a1[0]} a2_0={a2[0]}")
    var m = [[0, 0], [0, 0]]
    var row = m[0]
    row[1] = 5
    print("A2 m01={m[0][1]} row1={row[1]}")
    var t1 = "abc"
    var t2 = t1
    t2 = t2 + "X"
    print("T1 t1={t1} t2={t2}")

main()
```
