# native-build dies during module load and misreports it as a 7200s timeout

**Filed:** 2026-08-18
**Severity:** HIGH — two defects stacked: the native lane of the
engine-differential gate is 100% dark, and the error message actively
misdirects anyone who investigates.
**Status:** OPEN (diagnosis only; no fix attempted here).
**Found by:** the first full three-lane run of
`scripts/check/check-engine-differential.shs` on this tree.

**Binary under test:** `bin/simple` ->
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
sha256 prefix `4129e2a7d62e17a6`.

---

## Symptom 1 — the native lane answered nothing, 11 times out of 11

    [any_vs_typed_list_param] AGREE
      native: LANE_ERROR -- native-build produced no artifact
    [array_value_semantics] AGREE
      native: LANE_ERROR -- native-build produced no artifact
    ... (identical for all 11 fixtures) ...
    lane errors:       11 (failed closed -- not counted as divergence)

The harness handles this correctly in the sense that matters — a failed-closed
lane is never scored as a divergence, so this did **not** manufacture the gate's
FAIL (that is a genuine interpret-vs-jit defect, filed separately in
`jit_container_i64_boxing_truncation_2026-08-18.md`). But it means the gate has
been running as a **two-lane** comparison while reporting three lanes. Any
defect that lives only in the LLVM AOT lane is invisible, and would stay
invisible behind a green verdict. That is a fail-open, and it is the reason the
harness has a native lane at all: the original finding it was built to
mechanize (`native_slice_splits_utf8_three_divergent_policies_2026-08-01.md`)
was a *native-only* divergence.

## Symptom 2 — the reported cause is false

Reproduced directly on one fixture:

    $ bin/simple native-build test/fixtures/engine_differential/f64_roundtrip.spl -o /tmp/nb_f64.bin
    ...
    !!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
    error: native-build worker timed out after 7200s before producing a binary.
      The interpreted worker loads the whole compiler + LLVM import graph before any
      codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget. Raise
      --timeout, shrink --source, or use the in-process backend for cross-target builds.

    exit status: 255

**No build ran for 7200 seconds.** Timing, from the harness's own artifact
directory mtime to the run's completion:

| | |
|---|---|
| three-lane run, first `mkdir` of `build/engine_differential` | 09:11:52 |
| three-lane run complete (`/tmp/ed.done` written) | 09:43:56 |
| total wall time for **11** native builds | **1924s** |
| mean per native build | **~175s** |

If each of the 11 builds had genuinely timed out at 7200s the run would have
taken 79,200s — 22 hours. It took 32 minutes. The 7200s figure is not a
measurement; it is the *configured budget* printed as though it were elapsed
time.

## Mechanism

`src/app/cli/native_build_main.spl:304-322`. The parent classifies on the exit
code, and `code == -1` is a **sentinel shared by several distinct deaths** —
timeout, signal kill, and (as an earlier fix in this same block already
acknowledges) a Rust allocation abort:

    if code == -1 and native_build_output_has_alloc_failure(stdout, stderr):
        ... "ABORTED on a failed memory allocation (not a timeout)" ...
    else if code == -1:
        val secs = native_build_timeout_ms(args) / 1000
        eprint "error: native-build worker timed out after {secs}s before producing a binary."

The `else if code == -1` arm assumes any remaining `-1` is a timeout and prints
`native_build_timeout_ms(args)` — the budget, never the elapsed time. The
alloc-abort arm exists precisely because this misattribution had already sent
one investigation at the wrong defect
(`native_build_source_closure_zero_sources_2026-08-17.md`); the same trap is
still open for every other cause of `-1`.

Here the worker died with **no error of its own**. Its captured output ends
mid-module-load, in the `[gc-warning]` / `[use-warning]` stream, with no panic,
no allocation-failure text, and no codegen having started:

    [gc-warning] Higher-layer module 'std.nogc_sync_mut.daemon_sdk.protocol' ... (higher_layer_runtime_family)
    [use-warning] 'hash_text' is named in `use std.io_runtime.{...}` but module '.../io_runtime.spl' does not provide it ...

    !!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!

So the finding is: **the worker is dying ~175s into module loading, and the
parent relabels that as a two-hour timeout.**

## Why this matters beyond one gate

The prior session note on this ("`native-build` dying with `worker timed out`
and signal kills; one lane blamed host load but the process evidence refuted it
— 4 seconds of CPU over 11m45s at load 4.15 on 32 cores, blocked not
compute-starved") is the same defect seen from the other side. Note the
contrast with this run, where the worker was genuinely **compute-bound**
(measured 377s elapsed / 6:16 CPU on the first fixture — CPU ≈ wall, so not
blocked). Both were reported to the operator with the identical "timed out
after 7200s" string. A message that cannot distinguish a blocked process from a
saturated one from a killed one is worse than no message: it produced a
confident wrong hypothesis (host load) in at least one prior investigation.

## Suggested fix

1. **Measure, don't assume.** Record a start timestamp and print *elapsed*
   time. A message saying "died after 175s (budget 7200s)" would have made this
   self-evident and cost one clock read.
2. **Stop overloading `-1`.** `process_run_timeout_live` should distinguish a
   real timeout expiry from a child terminated by a signal, and report the
   signal number when there is one.
3. **Only claim a timeout when elapsed >= budget.** A one-line guard on the
   existing arm would have turned this entire investigation into a glance.

## Harness changes made in response (in this commit)

These do not fix the defect above; they stop the gate from hiding it.

- `run_native` no longer sends build output to `/dev/null`. It writes
  `build/engine_differential/<fixture>.build.log` and puts the first `error:`
  line into the LANE_ERROR note, so the reason appears in the gate output
  rather than requiring a manual re-run to discover.
- A lane that answered **zero** fixtures across the whole corpus is now named
  in a loud `DEGRADED COVERAGE` block, and the verdict downgrades to
  `PASS (DEGRADED) — ... lane(s) [native] answered nothing and are NOT covered
  by this verdict`. Still exit 0 — a two-lane comparison is real evidence and
  newly blocking pushes on a pre-existing condition would be its own harm — but
  it can no longer read as full three-lane coverage.
- Unknown lane names in `DIFF_LANES` are now rejected with `ERROR ... nothing
  was checked` (exit 2). Previously `SIMPLE_EXECUTION_MODE` silently selected
  the JIT for any unrecognised value, so `DIFF_LANES=interpret,jit,bogus`
  printed `PASS — 1 fixture(s) compared across 3 lane(s)` while only two engines
  ever ran — a phantom third lane agreeing with itself. Verified before and
  after.

## Related

- `doc/08_tracking/bug/jit_container_i64_boxing_truncation_2026-08-18.md` — the
  actual divergence currently failing the gate.
- `doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md`
  — the earlier investigation misdirected by this same `-1` misattribution.
- `doc/08_tracking/bug/native_slice_splits_utf8_three_divergent_policies_2026-08-01.md`
  — the native-only divergence that justifies the native lane existing.

## Verification of the harness changes (real runs, not reasoning)

`DIFF_FILTER=f64` with all three lanes, on the patched harness:

    [f64_roundtrip] AGREE
      interpret: sum=0.30000000000000004whole=2.0neg=-1.5tiny=0.000001big=1000000000000000000.0list_sum=6.875boxed0=1.5
      jit: sum=0.30000000000000004whole=2.0neg=-1.5tiny=0.000001big=1000000000000000000.0list_sum=6.875boxed0=1.5
      native: LANE_ERROR -- native-build produced no artifact: error: native-build worker timed out after 7200s before producing a binary. (full log: build/engine_differential/f64_roundtrip.build.log)
    ...
    PASS (DEGRADED) — 1 fixture(s) compared, 0 new divergences (0 baselined, 1 lane error(s)); lane(s) [native] answered nothing and are NOT covered by this verdict

exit 0. The LANE_ERROR note now carries the cause and a log path; the verdict
states its own degraded coverage. Compare the old output for the same
condition, which was the bare `native: LANE_ERROR -- native-build produced no
artifact` with a verdict claiming "across 3 lane(s)".

Unknown-lane rejection, exit code read directly into a variable rather than
through a pipe (a pipeline's `$?` is the last stage's status and has produced
false greens in this repo before — the first attempt at this check appeared to
exit 0 for exactly that reason):

    $ DIFF_LANES=interpret,jit,bogus DIFF_FILTER=f64 sh scripts/check/check-engine-differential.shs > /tmp/lane.log 2>&1; echo "real_exit=$?"
    real_exit=2
    $ tail -1 /tmp/lane.log
    ERROR — unknown lane 'bogus' in DIFF_LANES; SIMPLE_EXECUTION_MODE would silently run the JIT for it and report a phantom agreeing lane. Valid: interpret, interpreter, jit, native. Nothing was checked.

Before the change the identical command printed
`PASS — 1 fixture(s) compared across 3 lane(s), 0 new divergences` at exit 0.

No-regression check: the two-lane gate (`DIFF_LANES=interpret,jit`) returns the
same verdict before and after the patch —
`FAIL — 1 unbaselined divergence(s) among 11 fixture(s) compared`, with
`agreements: 9 / divergences: 2 (1 NEW) / lane errors: 0`.
