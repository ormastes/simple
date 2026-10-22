# Tree RSS floor kills the Stage 2 compiler-test phase on large hosts (exit 88)

Date: 2026-10-15
Host: Windows 11, 64 GiB RAM (66,865,260 KiB total, ~43 GiB available at start)
Lane: stage2 trust-root bootstrap, `--full-bootstrap --stop-after-stage2`,
12 workers (`--jobs=full`, memory-clamped from 24)

## Observation

`stage2-compiler-tests` was killed by the process-tree RSS watchdog:

```
status=rss-cap-exceeded
exit_status=88
max_rss_kib=5859375      # the historical floor, 5.59 GiB
peak_rss_kib=5862512
budget_ceiling_kib=8388608
```

Only `compiler_version` had run in the phase-verification matrix; the test
phase (build-threads=8, test-workers=4) never produced a result.

## Root cause

`scripts/bootstrap/lib/tree-rss-policy.shs`:

    cap = max(FLOOR 5859375 KiB, (base 3072 MiB + jobs * 96 MiB) * 1024)
    cap = min(cap, host_total * 50%), min(cap, hard ceiling)

For jobs=12 the budget is 4224 MiB < FLOOR, so the FLOOR wins; on a 64 GiB
host the 50% host bound (32 GiB) and the jobs-scaled ceiling (15.7 GiB) are
both far above the floor, so the floor is the operative cap. The floor is a
small-host lower bound, but on large hosts it becomes the effective ceiling.

The budget formula prices a worker at 96 MiB, calibrated for *compile*
workers (measured 57-76 MiB/worker in the header comment). The compiler-test
phase runs full compiler *binaries* as workers (each several hundred MiB),
so the phase's real peak (compile tree + test binaries) exceeds 5.59 GiB on
this host while still being well within physical memory.

## Workaround used

Per-run env knob, admitted under the policy's own ceiling math:

    SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=12582912   # 12 GiB < 15.7 GiB ceiling

## Suggested direction

Distinguish the floor's roles: it should lower-bound the cap on small hosts
but not upper-bound it on hosts where both the jobs-scaled ceiling and the
host-fraction are far higher. Options: (a) apply
`cap = min(max(budget, floor), ceiling, host_fraction)` only when host RAM
is unknown or small (e.g. host_total below some threshold); (b) let the test
phase resolve its cap from its own worker model (test workers priced like
compiler binaries, not compile workers); (c) keep the floor but raise the
per-worker price for non-compile phases. Any change must keep the documented
small-host protection and the watchdog's own ceiling recompute in
process-tree-rss-watchdog.pl consistent.

## Status (2026-10-16): fixed — option (b), phase-priced cap

`bootstrap_tree_rss_phase_cap_kib` (tree-rss-policy.shs) prices the Stage 2
compiler-tests phase by the host: `host_pct` of RAM clamped to
[floor, jobs-scaled ceiling]. bootstrap-from-scratch.sh uses it for that
phase only when no explicit `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` is set.
64 GiB host, 8 build threads: cap 16 GiB (was the 5.59 GiB floor). Small
hosts keep the host fraction (16 GB host -> 8,000,000 KiB). Selftest: 31
fixtures PASS incl. both phase-cap cases.

Note: on Windows the watchdog's "RSS" is the job object's commit charge
(`peak_job_commit_kib`), not working set; sampled working set of the same
builds stayed ~1-3 GiB while commit reached 5.9 GiB.
