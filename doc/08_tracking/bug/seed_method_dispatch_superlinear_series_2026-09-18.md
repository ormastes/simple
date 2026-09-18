# Seed interpreter: `impl Series:` method call cost grows superlinearly with receiver size

**Date:** 2026-09-18
**Found by:** lane L2 (`std.df` unique O(n²) fix), branch `work/acq-stdfix`
**Binary:** `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed)
**Severity:** perf regression. It hides algorithmic fixes in `std.df`.

## Symptom

After `unique_f64` was made O(n) with a local Dict, calling it as a
**method** is still superlinear:

| n (values) | `s.unique_f64()` wall |
|---|---|
| 5000 | 5.5 s |
| 10000 | 22.7 s |
| 20000 | 93 s |

That is about 4× per doubling. The byte-identical body written as a **free
function** that takes the `Series` as a parameter stays flat: n=10000 takes
1.9 s and n=20000 takes 2.0 s.

## Hypothesis (unverified)

The method-receiver path copies, or re-walks, the receiver's `values` array on
each field access inside the method body. Value semantics on `self` would make
every `self.values[i]` O(n).

## Repro

`test/01_unit/lib/df/df_unique_scaling_spec.spl` on `work/acq-stdfix`. Scale
the n=3000 case up and compare it with a free-function copy of `unique_f64`.

## Next

Profile `self.<array field>[i]` inside an `impl` method against the same access
on a parameter, on the seed. Check whether the pure-Simple interpreter
(`95.interp`) has the same behaviour.
