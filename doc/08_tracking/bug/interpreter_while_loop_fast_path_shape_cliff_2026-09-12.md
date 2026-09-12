# Interpreter: an equivalent loop body costs 47x more when the call sits inside a binary operand

- Status: OPEN (2026-09-12) — found by PERF-1 probe sweep; mechanism located, not fixed (widening the fast-path battery is an optimization change, not a contained fix)
- Found: 2026-09-12, interpreter component perf sweep (worktree simple-perf-1)
- Component: seed tree-walk interpreter —
  `src/compiler_rust/compiler/src/interpreter_control.rs` `exec_while`
  (the ten `try_exec_*_while_loop` pattern matchers at :362-400)
- Lane: interpreter only (`SIMPLE_EXECUTION_MODE=interpreter`). The JIT runs
  every shape below in 0.03 s.
- Binary: candidate seed built from origin/main 99c73a6ac87,
  `CARGO_TARGET_DIR=/home/yoon/cargo-perf1`, sha256 `bfab6d939b45...`

## Summary

`exec_while` opens with ten pattern matchers that execute a recognised loop
shape as a native Rust loop instead of walking the AST. A loop that matches one
of them runs ~1000x faster than the same work that does not match, and the
matcher set keys on the *syntactic shape of the assignment*, not on what the
loop computes. Two semantically identical loops therefore differ by 47x.

## Evidence (200,000 iterations each, `simple run`, interpreter lane)

| loop body (`fn add(a: i64, b: i64) -> i64: a + b`) | wall | per iteration | `interp-perf-counters` emitted? |
|---|---:|---:|---|
| `acc = add(acc, i)` | 0.02 s | ~50 ns | **no block at all** |
| `acc = acc + add(i, 0)` | 0.88-0.94 s | ~4.5 us | yes (`VT_CALLS 400000`) |
| `acc = acc + ident(i)` (`fn ident(x: i64) -> i64: x`) | 0.58-0.94 s | ~3-4.5 us | yes |
| `acc = ident(i)` | 0.60-1.15 s | ~3-5.7 us | yes |

Scaling the matched shape confirms it is not executing per iteration in the
tree-walker at all: `acc = add(acc, i)` at 2,000,000 iterations = 0.07 s and at
20,000,000 iterations = 0.11 s (100x the iterations for 1.6x the time).

`acc = add(acc, i)` matches `parse_two_arg_int_helper_loop`
(`try_exec_two_arg_int_helper_while_loop`, interpreter_control.rs:2094).
Wrapping the identical call in a binary operand matches no pattern, so the whole
loop falls back to the generic walk.

## Why this matters beyond the micro-benchmark

1. **Perf cliff in real code.** `x = x + f(y)` is the accumulate idiom that
   `src/lib/common/**` is written in; none of it matches a fast path.
2. **It silently invalidates scaling probes.** A ratio probe whose driver loop
   happens to match a matcher measures the matcher, not the interpreter. The
   reliable detector is the counters block: a run that emits **no**
   `interp-perf-counters:` block under `SIMPLE_PERF_COUNTERS=1` never entered a
   counted interpreter site, because the dump is registered lazily on first
   counter touch (`compiler/src/perf_counters.rs:88-113`). A block of all-zero
   counters (what a generic-walk loop with no COW clone prints) is NOT the same
   thing as no block.
   The landed `fn_call` "linear pin" is one of these: its loop body is
   `acc = add_i64(acc, i)`
   (`test/05_perf/interp/interpreter_component_scaling_spec.spl:263`), the
   matched shape exactly, and the numbers recorded in that spec's own header
   table — 67 us for n=20000 and 246 us for n=80000, i.e. **3.4 ns per
   iteration** — are three orders of magnitude below the ~4.5 us/iteration the
   generic walk costs. The pin is green, and it is pinning the fast path, not
   the interpreter's call cost. It should not be read as evidence about
   interpreted call overhead.
3. Loop-**condition** `.len()`/`.size()`/`.count()` hoisting
   (`try_hoist_loop_invariant_len`, same file) is a second shape-keyed
   optimization on the same path; invariant expressions in a loop BODY measured
   at or below an empty-body baseline in this sweep, so they cannot be measured
   by a naive "put the call in a loop" probe either.

## Repro

```sh
printf 'fn add(a: i64, b: i64) -> i64:\n    a + b\nfn main():\n    var acc = 0\n    var i = 0\n    while i < 200000:\n        acc = add(acc, i)\n        i = i + 1\n    print("{acc}")\n' > /tmp/fast.spl
sed 's/acc = add(acc, i)/acc = acc + add(i, 0)/' /tmp/fast.spl > /tmp/slow.spl
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_PERF_COUNTERS=1 time <seed> run /tmp/fast.spl   # ~0.02s, no counters block
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_PERF_COUNTERS=1 time <seed> run /tmp/slow.spl   # ~0.9s, counters block
```

## Fix direction (deliberately not taken here)

Either (a) extend the matcher set so a call in a binary operand of the
accumulator assignment is recognised — every existing alias/const/immutability
guard in `try_exec_two_arg_int_helper_while_loop` must be carried over, which is
why this is not a small change; or (b) reduce the generic path's ~4.5 us per
iteration so the cliff stops mattering. (a) widens an optimization, (b) is the
real fix; neither is a contained edit, so this is filed rather than attempted.

## Related

- `doc/08_tracking/bug/interp_tiered_jit_hotfunction_compiled_and_call_count_lost_2026-08-18.md`
- `doc/08_tracking/bug/seed_interpreter_raw_throughput_2026-08-21.md`
