# `print(<array>)` emits NOTHING on the native lane

- **Filed:** 2026-08-25
- **Status:** FIXED (verified 2026-11-11, lane work/p3-rt3-20261111 — aggregate print routing incl. runtime arrays landed via PR #7463; committed regression fixture passes native==interpret; see addendum below)
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

## 2026-11-11 triage — lane rt3 (worktree simple-p3-rt3-20261111, base 7f0fa174083, seed 46fe8f6b6def)

**Verdict: FIXED (root fix at tip; re-verified fresh on both lanes).**

- Root-cause fix is IN the tree at this base: `lower_bootstrap_print_call`
  (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2398-2450`)
  now routes aggregate arguments — explicitly including runtime-array locals via
  `arg_is_aggregate = self.runtime_array_locals.contains(arg_local.id)` (:2416),
  selected BEFORE any cstr/empty path — through `rt_to_string`, which renders the
  value by its own tag exactly like the interpreter oracle. Landed via merge
  4eb1de2ecbd (PR #7463, 2026-11-07, "mir-diverging-if-merges-batch2");
  confirmed ancestor of this base. This is precisely the missing runtime-array
  arm this doc's "Suspected area" predicted.
- Committed regression coverage exists and is gate-live:
  `test/fixtures/engine_differential/native_print_runtime_array.spl` (added by
  merge 9e7e7a526ed, PR #7597) is labeled "Regression for
  native_print_of_runtime_array_emits_nothing_2026-08-25" and is enumerated by
  `check_engine_differential.spl:list_fixtures()` (every `.spl` under
  `test/fixtures/engine_differential/` runs on interpret/JIT/native with
  byte-compared stdout).
- Fresh behavioral verification (this lane, tracked seed, Windows,
  `SIMPLE_NATIVE_BUILD_RUST=1`):
  - Doc minimal repro `p1.spl` (map/filter/lambda print): native
    `build/review/rt3/p1.exe` prints `[3, 6, 9, 12] / [3, 4] / 40`;
    interpret oracle prints byte-identical. rc=0 both lanes.
  - Committed regression fixture: native `npa.exe` prints
    `[2, 4, 6] / [2, 3] / [] / 17 / tail`; interpret byte-identical.
    Empty-filter array (`[]`) also renders — both outcomes of the
    runtime-array condition covered.
- Historical note: the 2026-08-25 "native-build broken at tip" blocker cited in
  this doc is long cleared; the native lane built both probes in ~7s each at
  this base.
