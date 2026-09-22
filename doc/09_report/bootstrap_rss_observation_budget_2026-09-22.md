# Bootstrap RSS observation budget — 2026-09-22

The macOS Phase 2/3 run [35677811307](https://github.com/ormastes/simple/actions/runs/35677811307)
on `575c18050346e8cd3ff92819cc60cb462450735b` stopped Stage 2 with exit 89:
`session observation exceeded sample budget`. The receipt recorded 30 samples,
peak 124,992 KiB against 5,859,375 KiB, and maximum sample gap 248.13 ms.
The local source-pinned producer independently hit the same error after 2,114
samples, peak 2,415,552 KiB and maximum gap 168.09 ms. These are measurement
deadline failures; neither receipt establishes a compiler crash or RSS breach.

The guard previously used its 100 ms scheduling interval as the deadline for
the full-system `ps` query plus authoritative SID observation. It now retains
the 100 ms target cadence and uses a separate, fixed 1,000 ms observation
deadline shared by both operations. It fails closed when observation hangs,
fails, or exceeds that budget. Slow successful samples add no cadence sleep.
Receipts expose the observation budget, maximum completed observation duration
and overrun count, alongside the existing maximum sample gap. This explicitly
relaxes the observation deadline; it is not a strict 100 ms sampling guarantee
or a kernel-enforced 6 GB memory cap. Allocation may grow between samples.

## Focused validation

`test/01_unit/scripts/process_tree_rss_observation_budget_test.shs` injects a
150 ms `ps` delay. Against the original guard it fails with exit 89 (`ps timed
out`); against this change it passes and checks honest timing/SID evidence.
It also verifies refusal to launch on a hung observer and anchored-root cleanup
with `quiescent=0` on persistent sampling failure after startup.

Passed once on macOS arm64:

- New observation-budget regression.
- `process_tree_rss_deadline_test.shs`: cadence, timeout/grace, bounded cold admission.
- `process_tree_rss_watchdog_test.shs`: RSS cap, startup, failure, fork/escape cleanup, stdin.
- `bootstrap_session_guard_test.shs`: nested sessions, helper integrity and SID escape.
- `process_tree_rss_identity_test.pl`: PID/PGID reuse and root identity anchor.
- `check-sosix-capsule-boundaries.shs`: 18 files/gates, zero violations; direct-rt 6,222/6,294.
- Perl syntax, `git diff --check`, working and staged direct-env-runtime guards.

The separate pre-existing `simpleos_process_session_honesty_test.c` fixture
could not link with the SoSIX include directory: `simpleos_test_alarm` has no
definition in its included source. No SoSIX runtime execution claim is made.
The capsule gate above is the completed SoSIX check.

## Paired elapsed time and memory

Compiled existing `fixture_process_tree_rss.c` with `cc -O2`; invoked it with
`16 normal <pid-file>` (16 MiB touched resident child, 2 second hold). Three
interleaved plain / original guard / revised guard runs used `/usr/bin/time -lp`.
Guard receipts measured aggregate observed workload RSS; `time` measured its
own maximum RSS statistic including helper compilation, not aggregate tree RSS.

| Mode | Elapsed seconds, runs 1/2/3 | Median seconds | Median time RSS bytes | Guard peak KiB, all runs |
| --- | --- | --- | --- | --- |
| Plain fixture | 2.66 / 2.25 / 2.25 | 2.25 | 17,809,408 | N/A |
| Original guard | 2.79 / 2.69 / 2.61 | 2.69 | 47,693,824 | 18,720 |
| Revised guard | 2.68 / 2.72 / 2.67 | 2.68 | 47,693,824 | 18,720 |

All nine executions exited zero. Revised maximum sample gaps were 105.08,
107.58 and 105.03 ms. The small sample shows no added elapsed/RSS regression;
existing guard startup overhead remains, and this is not bootstrap performance
acceptance. Raw profile files are retained locally at
`build/native_probe/rss-budget-profile/` in the fix worktree.

Independent Astra review approved the focused diff with no blocking findings.
It suggested optional future coverage of combined delayed `ps` plus delayed SID
budget exhaustion. No heavy bootstrap was run in this fix lane; the next
source-pinned producer must verify actual Stage 2/3 completion.
