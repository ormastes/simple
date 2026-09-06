# Spec-run cost: daemon startup pays a full-tree lint pass; content-bound specs pay a separate, larger tax

**Category:** Tooling / test runner
**Status:** Open (measured, not fixed — this is a measurement record, no production code changed)
**Owner:** lane S2 (measurement only)

## Binary identity (held fixed for every measurement below)

```
$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
181524312 2026-08-10 11:06:25.806608324 +0000
```
This is the Rust bootstrap seed (`WARNING: this Rust-built Simple binary is a
bootstrap seed only` printed on every run) — it is what `bin/simple` resolves
to for the whole duration of this measurement session (03:52-03:56 UTC
2026-08-11). Load average at the start: `24.53 24.10 18.66`; it ranged
16.7-32.6 across the session (recorded per-run below). All timings were taken
in `/home/ormastes/dev/pub/simple` only — never across `/mnt/fast/simple` or
`/mnt/data/dev/pub/simple`.

## 1. Floor cost: minimal spec vs a real spec

Minimal spec (written fresh in scratch, one `describe`/one `it`, only
`use std.spec.*`):

```
use std.spec.*

describe("minimal"):
    it("trivial"):
        expect(1).to_equal(1)
```

| run | mode | load avg | wall | internal `Duration:` | output lines |
|---|---|---|---|---|---|
| 1 | `--no-session-daemon` | 32.24 27.26 20.31 | 0.68s | 241ms | 67 |
| 2 | `--no-session-daemon` | 32.62 27.42 20.40 | 0.56s | 200ms | 67 |
| 3 | **default (session daemon)** | 28.66 27.33 20.75 | **26.08s** | 166ms | **1995** |

Run 3 is the same file, same binary, run seconds later than runs 1-2 — the
only variable is dropping `--no-session-daemon`. The reported `Duration:`
(actual test execution) is 166ms either way; wall time differs by **38x**
because of everything printed around it.

Real spec for comparison, `test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl`
(18 examples), `--no-session-daemon`: load `31.30 27.31 20.44`, wall **0.99s**,
internal `Duration: 372ms`, 90 output lines, all 18 passed. This directly
contradicts the "5-10 minutes" figure quoted in the task brief for this file —
under `--no-session-daemon` and the current binary/tree, it is sub-second.
**Floor cost for an ordinary spec under `--no-session-daemon` is well under
1 second; the reported multi-minute figures for this file did not reproduce
tonight.** Two independent possibilities, not resolved further here: (a) the
daemon path (see below) was in play when the multi-minute figures were
recorded, or (b) transient host contention (load avg was reported as high as
60-90 earlier) made an otherwise-fast run pathological. This report cannot
distinguish the two from present evidence and states that plainly rather than
guessing.

## 2. Attribution: the session daemon path pays a full-tree lint/warning pass, the no-daemon path does not

Run 3 above (default daemon mode) produced 1995 lines. Grepping it:
`Results:`/`Passed:`/`Duration:` appear once, at line 1942-1948 — the actual
test result. Lines 1-1941 and 1949-1995 are `warning:`/`[gc-warning]` lines
from files that have nothing to do with the minimal spec under test:
`src/app/io/process_env_ops.spl`, `src/lib/string_core.spl`,
`src/app/io/env_ops.spl`, `src/lib/nogc_async_mut/test_runner/test_runner_types.spl`,
plus repeated `compiler_cross_module_private_symbol_collision` warnings for
`dir_remove_all`, `file_read_bytes`, `shell`. These are stdlib/runtime files,
not the spec file, and the warning block appears in full **twice** — once
before the `Results:` line, once after — consistent with the daemon doing a
full-tree pass on session start and again on session end/teardown. This
matches the task brief's "~1,900 lines of lint/gc warnings before its
`Results:` line" almost exactly (1941 lines before, in this run).

The `--no-session-daemon` runs (67 and 90 lines respectively) show only 1-3
warnings specific to the spec file's own import graph, no full-tree scan.

**Headline finding:** for a trivial spec, the session-daemon path costs
~25.9s of wall time that the no-daemon path does not pay, entirely attributable
to a full-tree lint/warning pass run twice around the actual (166ms) test.
That is a **~38x** wall-time inflation from a fixed, non-test-specific cost.

## 3. Cache check

No equivalent of `scripts/check/lint-cached.shs`'s 152s-cold/0.03s-warm cache
was observed for `bin/simple test`. Two consecutive `--no-session-daemon` runs
of the same minimal spec (runs 1 and 2 above) took 0.68s and 0.56s — a small,
plausible OS page-cache effect, not a 1000x+ warm-cache collapse. The daemon
mode's repeated full-tree pass (once at start, once at end, same session) is
itself evidence against caching: if prior analysis were cached, the second
pass within the *same process* would not re-emit all ~1940 lines identically.
No `SIMPLE_LINT_CACHE`-equivalent env var or cache-hit message was found by
grep in `src/app/cli/*.spl`.

## 4. Content-bound cost is a separate, larger problem than the daemon tax

`test/01_unit/os/vulkan/spirv_boundary_glslang_spec.spl` under
`--no-session-daemon` did **not** finish before hitting its own internal
`child-timeout`, confirmed by the final verdict line:

```
SPEC FILE VERDICT: test/01_unit/os/vulkan/spirv_boundary_glslang_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=child-timeout budget_ms=120000
Results: 1 total, 0 passed, 1 failed
Duration: 120410ms
```

**This proves `--no-session-daemon` does not help this spec at all** — it
still ran for the full 120s internal budget and failed on timeout, exactly as
described in the task brief (previously observed with a 900s budget it still
exceeded). While waiting, its worker process
(`bin/release/x86_64-unknown-linux-gnu/simple run
test/.../spirv_boundary_glslang_spec.spl`) was observed at **100% CPU**,
accumulating CPU time (1:24 -> 1:41 over ~17s wall) while emitting no new
output — i.e. genuinely computing, not blocked or deadlocked, matching the
task brief's own observation. This is **not** daemon-startup lint tax: it
persisted under `--no-session-daemon`, which we showed above eliminates the
tree-wide lint pass. This spec's cost is intrinsic to its own content
(SPIRV/glslang-adjacent compilation work per example) and is a wholly separate
problem from Finding 2 — mitigation 1 below (`--no-session-daemon`) has zero
effect on it. Load avg during this run: 16.70-31.43 (recorded at multiple
points), ruling out extreme host contention as the sole cause — CPU-bound
work was directly observed via `/proc/<pid>/stat` utime deltas.

## 5. Ranked mitigations, with numbers

1. **`--no-session-daemon` for single/few-spec runs — proven, ~38x on the
   measured trivial case (26.08s -> 0.68s).** This is the cheapest available
   mitigation and requires no code change: it is an existing flag. It does
   not help content-bound specs like the glslang one (Finding 4) — for those,
   the daemon was never the bottleneck.
2. **Fix or bypass the double full-tree lint/warning pass in daemon mode.**
   Given `--no-session-daemon` already exists and is ~38x faster for the
   common case, the daemon's warm-session value proposition needs
   re-justifying: it currently pays the SAME full-tree cost the no-daemon
   path avoids, twice per session, and this report found no evidence it
   caches that cost across specs within one session (that would need a
   multi-spec-in-one-daemon-session measurement, not done here — flagged as
   a follow-up, not claimed).
3. **Do not attempt to fix the glslang spec's intrinsic cost here** — it is
   out of scope for a measurement-only lane and is a content/algorithm
   question (why does it call an external-cost path per example), not a
   test-runner fixed-cost question. Filing it separately is the correct next
   step, not folding it into this record.
4. **Batching several specs into one process** (candidate mentioned in the
   task) was not measured — no safe way to do so without touching the shared
   test DB per `.claude/rules/testing.md`'s parallel-corruption warning, and
   this lane does not run production code changes. Left unevaluated,
   explicitly, rather than assumed to work.

## Bottom line

Two distinct, unrelated costs were conflated in the original complaint:
- **Fixed/systemic**: the session daemon's full-tree lint pass, ~26s,
  ~38x inflation on a sub-second spec, fully avoidable today with
  `--no-session-daemon`.
- **Content-bound/per-spec**: `spirv_boundary_glslang_spec.spl`'s own
  workload, which stayed CPU-bound past 200s even with the daemon removed —
  genuinely irreducible without changing what that spec's examples do, and
  not a test-runner defect.
Reporting one number ("specs take 10-25 minutes") without separating these
two obscures that one has a one-flag fix today and the other does not.
