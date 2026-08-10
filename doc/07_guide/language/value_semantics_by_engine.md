# Value vs Alias Semantics, Per Engine (measured 2026-08-10)

> **RE-MEASURED 2026-08-10 on a FRESH seed build — the table below describes a
> STALE binary.** The deployed `bin/release/x86_64-unknown-linux-gnu/simple`
> used for the original measurement was built 2026-08-09 04:50, BEFORE the
> F1 struct-value-semantics campaign landed the same day (`735bbd4b606` S3
> declaration-kind carry, `cf992112a2d` S5 AggregateCopy sites F–I,
> `9106761fe76` S6 param-copy site J). On a fresh
> `src/compiler_rust/target/release/simple` (cargo build, 59,000,784 bytes,
> mtime 2026-08-10 04:16), the 6-position matrix CONVERGES on 5 of 6:
>
> | Position | Interp | JIT (fresh seed) |
> |---|---|---|
> | plain assignment | copy (1.0) | **copy (1.0)** |
> | nested struct field via copy (`o2.inner.a=9.0`) | copy (1.0) | **STILL ALIAS (9.0)** |
> | argument passing | copy (1.0) | copy (1.0) |
> | return value | copy (1.0) | copy (1.0) |
> | list element extraction | copy (1.0) | copy (1.0) |
> | dict value extraction | copy (1.0) | copy (1.0) |
>
> Residual defect: `AggregateCopy` is SHALLOW — a struct-typed field is stored
> as a pointer, so copying the outer struct aliases the inner one. Filed in
> the bug doc (residual section). `m[1][0]=9` divergence UNCHANGED on the
> fresh seed (interp rejects, JIT works). Everything below is the stale-binary
> record, kept for provenance.

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
- **Dict field inside a `struct`, mutated through a by-value receiver — now
  MEASURED, and it diverges** (2026-08-10): `self.values[k] = v` in a free
  function taking a `struct` by value is a silent **no-op in the interpreter**
  and **persists in JIT and native/AOT**. Same probe, absence-controlled, three
  engines. The `class` twin persists everywhere. The intended copy DEPTH for a
  collection-valued struct field is **undocumented** — see
  `doc/08_tracking/bug/struct_dict_field_mutation_engine_divergence_2026-08-10.md`
  for the matrix, the design question, and the production blast radius.
  Until it is decided: never mutate a collection field through a by-value
  struct — the result depends on the lane.
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

Native/AOT (`native-build`) status: **MEASURED 2026-08-10.** The llc
void-type blocker does NOT reproduce at current WC: the guard in
`translate_alloc` (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
~L2015-2026, landed 2026-08-08) backs void-typed spill slots with `i64`, and
`native-build` interprets the WC compiler `.spl` live, so both the minimal
probe and the full matrix now build and RUN. Binary:
`bin/release/x86_64-unknown-linux-gnu/simple` (29,577,536 B, mtime
2026-08-09 04:50; the 2026-08-10 04:16 seed named in the bug doc no longer
exists, and a freshly rebuilt seed cannot reach the backend due to unrelated
WC semantic drift). Measured AOT column (i64-field probes, printed values):

| Position | AOT (native-build) |
|---|---|
| plain assignment (`var b = a; b.n = 2`) | **COPY** (a.n=1) |
| argument passing (callee sets `.n=100`) | **COPY** (c.n=3) |
| return value | copy-consistent (r.n=6) |
| list element extraction (`var e = lst[0]; e.n = 11`) | **ALIAS** (lst[0].n=11) |
| dict value extraction (`var dv = d["k"]; dv.n = 21`) | **ALIAS** (d["k"].n=21) |
| nested struct field (`var o2 = o; o2.inner.v = 31`) | **COPY** (o.inner.v=30) |
| arrays (`var arr2 = arr; arr2[0] = 9`) | COPY (arr[0]=1) |
| text | COPY (t=abc) |
| `m[1][0] = 9` | ACCEPTED and works (m10=9); extracted row not aliased (row0=3) |

So AOT matches neither other lane exactly: it copies where the post-F1 JIT
copies AND on the nested-field case (where JIT still aliases via shallow
`AggregateCopy`), but **container extraction (list AND dict) aliases under
AOT** where interp and post-F1 JIT copy. New AOT-only defect observed while
measuring: an `f64` struct field interpolated into text prints its **raw i64
bit pattern** (`f.a=4607182418800017408` for 1.0) — the copy/alias verdict
for the f64 probe was still readable from the distinct bit patterns
(1.0 vs 7.0 = COPY). Durable gate: `scripts/check/check-aot-smoke.shs`
(native-builds, runs, and output-asserts a struct probe; PASS/FAIL/ERROR
verdict convention).

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
