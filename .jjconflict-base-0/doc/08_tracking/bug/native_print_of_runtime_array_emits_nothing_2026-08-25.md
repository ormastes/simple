# `print(<array>)` emits NOTHING on the native lane

- **Filed:** 2026-08-25
- **Status:** RESOLVED 2026-09-02 (the native lane prints runtime arrays -- see the RESOLVED section at the bottom). Was: OPEN
- **Lane:** native (`native-build`) only. Both seed lanes (`interpret`, `jit`) are correct.
- **Found by:** `scripts/check/check-engine-differential.shs`, fixture
  `test/fixtures/engine_differential/closure_runtime_facing.spl`, while clearing
  that fixture's `unresolved method call: find` LANE_ERROR.

## Symptom

A `print()` whose argument is a runtime array produces **no output at all** on
the native lane — not `[]`, not `nil`, not a crash. The surrounding prints in
the same program are correct, so the program looks like it merely printed less.

## Reproduce (minimal, uses only long-standing code paths)

`scratch/gf/p1.spl`:

```
fn main() -> i64:
    val xs = [1, 2, 3, 4]
    print(xs.map(\x: x * 3))
    print(xs.filter(\x: x > 2))
    val f = \x: x * 10
    print(f(4))
    0
```

Measured at `5f2ad54578f` (see "Why this commit" below):

```
$ ./bin/simple native-build scratch/gf/p1.spl -o /tmp/p1.bin   # rc=0, artifact produced
$ /tmp/p1.bin
40

$ SIMPLE_EXECUTION_MODE=interpret ./bin/simple run scratch/gf/p1.spl
[3, 6, 9, 12]
[3, 4]
40
```

Two of the three prints vanish. `40` proves the program ran to completion and
that the lambda/closure machinery itself is fine — only the array prints are
lost.

## Not caused by the `find`/`get` lowering

This probe deliberately calls **only** `map` and `filter`, whose lowerings
(`lower_array_map` / `lower_array_filter` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`) are
long-standing and were not touched by the `get`/`find` change filed alongside
this record. The probe contains no `.get(` and no `.find(`, so none of the new
code can execute for it: the new dispatch arms are gated on the method name,
and the new `lower_array_find` has no other caller. (The probe was run with
that change applied; it exercises only untouched paths.)

## Effect on the differential gate

`closure_runtime_facing.spl` prints four arrays (`map`, `filter`, a
capturing-lambda `map`, and `words.map(\s: s.len())`). Until the `find` gap was
closed, the whole fixture died earlier with
`MIR lowering error: unresolved method call: find`, so the gate classified it as
a LANE_ERROR and it never reached a value comparison. With `find` lowered, the
fixture builds and runs, and this defect becomes visible as a real DIVERGENCE:

```
seed lanes (interpret and jit, identical):
    [3, 6, 9, 12]
    [3, 4]
    3
    [11, 12, 13, 14]
    [1, 2, 3]
    40
    8

native lane:
    3408
```

Whitespace-stripped, that is `[3,6,9,12][3,4]3[11,12,13,14][1,2,3]408` vs
`3408`: every scalar agrees (`find` → `3`, `f(4)` → `40`, `g(3,5)` → `8`) and
every array print is missing.

**This divergence is not new — it was masked.** The fixture was never compared
on any engine before, so the gate reported a LANE_ERROR where a wrong answer was
already present underneath.

## Do NOT baseline this fixture

`scripts/check/check_engine_differential.spl`'s `baselines()` carries an
explicit rule: *"Baseline only a divergence that has been DECIDED to be
acceptable, not merely one that is known"*, and *"weakening a correct failing
check to make CI green is exactly what this harness exists to prevent"*. The
list is currently EMPTY and that is its correct state. Silently dropping an
array's contents on one lane is a wrong answer, not an accepted trade, so this
fixture must stay unbaselined until the defect is fixed.

## Suspected area (not yet root-caused)

The lost values are all locals registered in `runtime_array_locals` /
`mark_runtime_value_local` — array handles rather than scalars. The `print`
lowering path appears not to have a runtime-array arm, so the argument is
lowered to something the emitted call renders as empty. Start at the `print`
call lowering in `src/compiler/50.mir/` and at the `runtime_array_locals`
consumers listed by
`/usr/bin/grep -rn runtime_array_locals src/compiler/50.mir/`.

## Why the measurement is at `5f2ad54578f` and not at the tip

`native-build` is broken outright at `origin/main` `e8db788629b` — **every**
native build, including a three-line hello world, fails after the link step
with `error: semantic: type mismatch: cannot convert array to int`. That is a
separate regression, filed as
`native_build_broken_at_tip_cannot_convert_array_to_int_2026-08-25.md`. The
native lane last worked at `5f2ad54578f`, so all native measurements in this
record were taken there. `origin/main` has since moved on to `73d6deb5f66`,
which has not been probed.

---

## RESOLVED 2026-09-02 — the native lane prints runtime arrays

Host aarch64-apple-darwin. Binary: `src/compiler_rust/target/release/simple` (Rust seed, 37,291,896 B, 2026-09-01 09:24). `bin/simple` on this host is the BOOTSTRAP cli (`simple-bootstrap 1.0.0-beta`, `compile`/`native-build` only) and answers `unknown command 'run'`, so it is NOT the lane used below., native lane = `native-build` of the program then running the produced
binary.

```
val xs = [1, 2, 3, 4]
print(xs)                 -> [1, 2, 3, 4]
print(xs.map(\x: x * 3))  -> [3, 6, 9, 12]
print("A_done")           -> A_done
```

Both the plain array and the `map` result print, and the surrounding print is
still correct, so this is not a "printed less" ordering artifact. The filed
symptom -- no output at all for an array argument -- does not occur. Marking
RESOLVED.
