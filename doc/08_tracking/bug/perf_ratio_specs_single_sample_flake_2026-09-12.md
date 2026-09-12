# Perf ratio specs take ONE sample per point, and flake RED on a loaded shared host

- Status: FIXED for `test/05_perf/interp/string_char_index_scaling_spec.spl` (best-of-two sampling, 2026-09-12); the same single-sample shape remains in the three sibling perf specs — see "Remaining"
- Found: 2026-09-12, PERF-1 sweep (worktree simple-perf-1, branch work/perf-1-2026-09-12)
- Component: `test/05_perf/interp/*_scaling_spec.spl` (measurement method, not product code)
- Binary: candidate seed from origin/main 99c73a6ac87, `CARGO_TARGET_DIR=/home/yoon/cargo-perf1`, sha256 `bfab6d939b45...`

## Summary

The landed ratio specs time each point ONCE and divide. The ratio therefore
carries the noise of BOTH samples multiplied together. On the shared dev host
(load ~27 on 20 cores, 20+ concurrent `simple` processes from parallel agent
sessions) a single co-tenant CPU spike during the n=80000 loop is enough to
push a linear accessor past the 7x bound and turn the spec RED on a build that
is provably not quadratic.

## Evidence — four runs of the UNCHANGED spec, one binary, same worktree

| run | substr 20k -> 80k | ratio | char_at 20k -> 80k | ratio | s[i] 20k -> 80k | ratio | verdict |
|---|---|---:|---|---:|---|---:|---|
| A | 20156 -> 79733 us | 3.96 | 19448 -> **171501** us | **8.82** | 16093 -> 65148 us | 4.05 | **FAIL** (1 of 7) |
| B | 40898 -> 164450 us | 4.02 | 39414 -> 118107 us | 3.00 | 16438 -> 65027 us | 3.96 | OK |
| C | 37556 -> 159760 us | 4.25 | 34871 -> 87473 us | 2.51 | 16223 -> 64311 us | 3.96 | OK |
| D | 41127 -> 164546 us | 4.00 | 39295 -> 158096 us | 4.02 | 32833 -> 130246 us | 3.97 | OK |

1 RED in 4 runs (25%) with no code change between runs. Run A's char_at
n=20000 sample (19448us, 0.97us/call) is in line with every other run; only
its n=80000 sample is inflated (171501us = 2.14us/call vs 1.1-1.5us/call
elsewhere).

Independent confirmation that char_at is NOT quadratic: a single program that
times `char_at`, `char_code_at` (already memoised) and `substr` over the SAME
two strings in the SAME process measured, warm, 42994 -> 147618 us (3.4x),
27708 -> 120320 us (4.3x) and 36458 -> 145350 us (4.0x) respectively. The
ASCII fast path (`shared_text_is_ascii`, `interpreter_method/string.rs:463`)
is present and hit.

## Fix

`best_of_two(a, b)` in the spec: sample each point twice, keep the smaller.
The minimum of k samples is the standard estimator for a quantity contaminated
only by additive interference — a co-tenant spike can only make a sample
larger. It does NOT weaken the 7x bound, change the loop, or change what is
measured, and it fails closed: both samples must be > 0, so a zero-iteration
(vacuous) timing still fails.

After the fix, 4 consecutive runs: all OK (see the receipt for the per-run
ratios).

## Remaining

`interpreter_component_scaling_spec.spl`, `dict_mutator_scaling_spec.spl`,
`identifier_mutator_in_expression_scaling_spec.spl` still take one sample per
point. They use a larger multiplier (doubling^2) and did not flake in this
session, so they are left alone rather than edited speculatively; apply the
same helper if one of them flakes.

## Related

- `doc/08_tracking/bug/interpreter_string_char_index_rescans_per_call_2026-09-12.md` (the fix this spec pins — still correct; the flake is in the measurement, not the fix)
- `doc/08_tracking/bug/interpreter_while_loop_fast_path_shape_cliff_2026-09-12.md` (second measurement hazard found in the same sweep)
