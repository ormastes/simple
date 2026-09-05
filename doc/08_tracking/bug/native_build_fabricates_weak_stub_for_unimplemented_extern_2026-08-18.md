# native-build fabricates a WEAK stub for an unimplemented `extern fn`, which returns garbage at runtime — and the guard misses it because it is weak

Status: OPEN (P1) — silent wrong answer, plus a fail-open in the guard meant to catch exactly this.

## Two defects, found together

### Defect 1 — the build silently fabricates a stub that returns garbage

An `@extern fn` with **no implementation anywhere** must fail the build. It does not.

Fixture (`absent.spl`):

```
extern fn lane_definitely_absent_probe(x: i64) -> i64

fn main() -> i64:
    val r = lane_definitely_absent_probe(7)
    print "got {r}"
    0
```

```
$ SIMPLE_NATIVE_BUILD_RUST=1 bin/simple native-build --entry absent.spl -o absent.bin
BUILD_RC=0                                   # no error, no diagnostic
$ ls absent.bin                              # 23896 bytes, executable
$ nm -a absent.bin | grep lane_definitely_absent
0000000000402eb9 W lane_definitely_absent_probe      # <-- FABRICATED, weak
$ ./absent.bin
got 3
RUN_RC=0
```

The call returns **3** — not the argument, not an error, not a crash. A program
calling an unimplemented extern compiles clean, runs clean, and produces a
fabricated value. That is the worst failure class available: no signal at any
stage.

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple`, md5
`f4d7a685e131bc863042322ce25c8f88` (seed rebuilt 2026-08-17 20:28, at
1.0.0-RC).

### Defect 2 — `check-native-extern-fabrication.shs` cannot see it

The guard exists specifically to catch fabrication. On the same fixture it
reports:

```
FAIL — [default] native-build exited 0, no fabricated symbol found by nm, and no
       diagnostic was printed. This is an UNEXPECTED third outcome — investigate
       manually rather than trusting either known state.
```

"no fabricated symbol found by nm" is **wrong** — `nm` shows the symbol plainly.
The guard's `nm` matching does not account for the **`W` (weak)** symbol class,
so the fabrication it was written to detect walks straight past it and is
reported as an unclassifiable third state.

This is a fail-open in a guard wired into the pre-push hook: the one case it
must never miss is the one it misses. Its FAIL here is accidental — it fails for
"I do not understand this outcome", not "I caught fabrication".

## Why this surfaced only now

The guard normally dies before reaching this point: the default worker path
OOMs (see `prepush_hook_unpassable_native_build_oom_2026-08-17.md`), so the
guard exits 143 having assessed nothing. Running it with
`SIMPLE_NATIVE_BUILD_RUST=1` routes native-build through the healthy in-process
Rust backend (134 MB / 13.5 s vs 12.3 GB / 8m36s), which lets the guard reach a
real verdict — and the real verdict exposes both defects above.

## Scope note — the two lanes are NOT behaviourally identical

This is a direct argument against casually switching the default to
`SIMPLE_NATIVE_BUILD_RUST=1` as an OOM mitigation. The in-process lane is
dramatically cheaper, but on this fixture it accepts an unimplemented extern
where the worker lane refused. Any adoption decision must treat the lanes as
semantically different, not as a fast path and a slow path to the same result.

## Exit criteria

1. `native-build` fails, with a diagnostic naming the symbol, when an
   `@extern fn` has no implementation — on BOTH lanes.
2. `check-native-extern-fabrication.shs` classifies a weak (`W`) symbol as
   fabrication, and its `--selftest` gains a fixture asserting exactly that
   (a weak-symbol binary must be detected), so the hole cannot silently return.
3. No fixture exists for which the build exits 0 and the program returns a
   fabricated value.
