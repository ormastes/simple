# Widget Showcase Frame Distribution Is Not Yet Verified

## Partially resolved 2026-11-25 (release/1.0.0, worktree wt-p3-baf) — spec realigned to the landed p50/p95 fix; one example remains environment-blocked

Runner limitation stated up front: the only runnable binary here is the
tracked `bin/simple.exe` (38,403,072 bytes), which self-identifies with the
Rust-bootstrap-seed warning banner. It parses and runs current source, but it
is NOT the "accepted source-matched pure-Simple runner" the Remaining
Verification list asks for, and the wrapper's own identity gate
(`scripts/check/lib/require-self-hosted.shs` `binary_is_seed`) would reject it
for real perf evidence. Results below are diagnostic contract evidence, not
performance qualification.

**What was stale and is now fixed.** The spec's "emits retained frame p50 and
p95 timing fields for real runs" example still pinned the pre-fix wrapper
(`frame_p50_ns=$frame_avg_ns` / `frame_p95_ns=$frame_avg_ns` — the
mean-copy this bug was filed about). The landed wrapper computes real
distribution values: it parses per-frame `frame_p50_ns`/`frame_p95_ns`/
`warmup_frames`/`frame_sample_count` from the probe log
(`check-widget-showcase-4k-200fps.shs:936-939`), gates them with
`frame_distribution_status` (warmup positive, sample count == frames, p95 not
below p50, `:552-565`, `:951-956`), and fails closed with
`frame-distribution-untrusted`. The example was updated to assert that real
wiring, including negative assertions that the mean-copy lines are gone. This
is an assertion correction toward the documented fix, not a weakening.

**Measured before → after** (this worktree, `SIMPLE_LIB=src bin/simple.exe test
test/03_system/check/widget_showcase_perf_wrapper_spec.spl --mode=interpreter`):

- Before (and note: the worktree's sparse checkout excludes `/examples/`; the
  spec reads `examples/06_io/ui/widget_showcase_gui.spl`, so it was first run
  with `examples/` materialized): 4 passed / 2 failed.
- After the spec realignment: **5 passed / 1 failed**.

**The remaining failure is environment-blocked, not a product regression.**
"does not let impossible producer timing pass a slow retained probe" drives a
fake `SIMPLE_BIN` through a real (non-plan-only) wrapper run and expects
`reason=below-200fps`. Three fail-closed gates added after the spec was
written now stand in front of that path:

1. The 2026-07-28 binary-identity gate rejects the fixture's `fake-simple`
   (`simple-binary-identity-unverifiable`) because it has no `--version`
   banner — this is the observed failure and is the hardening working as
   designed.
2. Past that, `load_perf_baseline` requires a fully admitted
   `GUI_SHOWCASE_PERF_BASELINE_ENV` (schema `widget-showcase-perf-v2`,
   source-revision match, artifact sha256, machine-identity bucket); the
   fixture supplies none.
3. Past that, `compare_perf_baseline` requires a measured `max_rss_kb` from
   `/usr/bin/time -v`, which does not exist on this Windows/Git Bash host, so
   the `below-200fps` decision row is unreachable here regardless of fixture.

Reaching `below-200fps` again needs a Linux host with `/usr/bin/time` and a
fixture that builds a valid admitted baseline (or a wrapper-provided test
hook). Left failing deliberately: rewriting its expected reason to an earlier
gate's reason would silently drop the impossible-timing coverage. Tracked as
the follow-up below.

**Follow-up (new, bounded):** teach the impossible-timing example to fabricate
a valid admitted baseline (or add a wrapper test hook that bypasses
identity/baseline/RSS gates explicitly for fixture runs) on a Linux runner,
so the `below-200fps` rejection is exercised again.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Problem

The retained 4K/8K wrapper reported p50 and p95 by copying the arithmetic
mean. Those rows were not distribution evidence.

## Current Fix

- The showcase performs 12 warmup presents.
- It records each of the 200 measured present durations.
- It computes and emits real p50/p95 values plus sample and warmup counts.
- The wrapper fails closed unless the sample count equals the requested frame
  count, warmup is positive, and p95 is not below p50.
- The aggregate completion gate requires the same counts.

## Remaining Verification

1. In a fresh session, run
   `test/03_system/check/widget_showcase_perf_wrapper_spec.spl` once with an
   accepted source-matched pure-Simple runner and retain named failure output.
2. Generate the SSpec manual only after that focused run passes.
3. Run real native 4K and 8K probes on a qualifying Vulkan host and retain both
   `status.env` rows, logs, timing logs, readback checksums, RSS, and source
   provenance.

The latest diagnostic run was capped at 7/9 after three cycles. It is not a
performance qualification, and no 4K/8K FPS claim is valid yet.

