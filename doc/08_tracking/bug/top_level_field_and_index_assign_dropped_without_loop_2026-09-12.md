# Top-level field and index assignment to a module-level `var` is silently dropped — no loop required

- **Id:** top_level_field_and_index_assign_dropped_without_loop_2026-09-12
- Status: OPEN (2026-09-12)
- **Severity:** P1 — silent wrong results, no error, on both engines
- **Found:** 2026-09-12, while re-checking
  `interp_struct_local_copy_aliasing_2026-07-22` (bug fan-out shard 01)
- **Component:** Rust seed, module-level statement execution
- **Binary:** `bin/simple` = `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1`, aarch64 host

## Relationship to the existing row

`top_level_array_index_assign_in_loop_silently_dropped_2026-08-25.md` records
the same loss for `arr[i] = …` **inside a top-level `for`/`while` loop** and
attributes it to loop bodies treating a module-level collection as a copied
temporary. **The loop is not the axis.** This row widens the claim on measured
evidence: a single straight-line top-level statement loses the write too, and
so does struct **field** assignment, which that row does not mention at all.

## Repro

```simple
struct S:
    x: i64

fn in_fn() -> str:
    var d = S { x: 1 }
    d.x = 2
    var a: [i64] = [1, 2]
    a[0] = 7
    return "fn d.x=" + str(d.x) + " a0=" + str(a[0])

var gs = S { x: 1 }
var ga: [i64] = [1, 2]

fn writes_global() -> i64:
    gs.x = 3
    ga[0] = 8
    return 0

print in_fn()
val ignored = writes_global()
print "after-call gs.x=" + str(gs.x) + " ga0=" + str(ga[0])
gs.x = 4
ga[0] = 9
print "toplevel gs.x=" + str(gs.x) + " ga0=" + str(ga[0])
```

Identical output on `bin/simple run` (JIT) and on
`SIMPLE_EXECUTION_MODE=interpreter`:

```
fn d.x=2 a0=7
after-call gs.x=3 ga0=8
toplevel gs.x=3 ga0=8          <- gs.x=4 and ga[0]=9 were both DROPPED
```

## The axis, by bisection

| where the write happens | target | result |
|---|---|---|
| inside a `fn` | local struct field | **works** (`d.x=2`) |
| inside a `fn` | local array element | **works** (`a0=7`) |
| inside a `fn` | module-level struct field | **works** (`gs.x=3`) |
| inside a `fn` | module-level array element | **works** (`ga0=8`) |
| top-level statement | module-level struct field | **DROPPED** |
| top-level statement | module-level array element | **DROPPED** |
| top-level statement | module-level scalar (`n = 5`) | works |

So the axis is **top-level statement position**, not the loop, not the engine,
and not the declaration site of the variable. A whole-variable reassignment at
top level is fine; only a *place* write (field or index) through a module-level
`var` is lost. No loop is needed and no diagnostic is produced.

Second, smaller form (no function in the file at all):

```simple
struct S:
    x: i64

var direct = S { x: 1 }
direct.x = 2
print "direct.x=" + str(direct.x)     # prints 1
```

## Impact

- sdoctest/README blocks are module-level statements, so any documented example
  that mutates a struct field or an array element asserts the wrong oracle.
  This is the same blast radius the 2026-08-25 row describes, but larger,
  because it now includes every non-loop example and every struct field.
- Any top-level script that builds state by place-assignment is silently wrong.
  The workaround in the sibling row (wrap the mutation in a `fn`) is confirmed
  effective here: every in-function row above is correct.

## Fix direction

Module-level statement execution appears to evaluate a place expression against
a **copy** of the module global rather than against its live storage, and never
writes back. Note the asymmetry that pins it: the same write performed from
inside a callee frame reaches the live global (`gs.x=3` is observable
afterwards), so the storage itself is shared and addressable — it is the
top-level statement path that loses the reference. Likely area, same as the
sibling row: the seed's module-level statement executor
(`src/compiler_rust/compiler/src/interpreter*`, JIT
`ExecCore::run_file_interpreted_with_args`).

Not fixed here: seed-side, out of scope for a pure-Simple bugfix lane.
No spec is added, because a spec asserting the correct behaviour would be a
committed failing test.
