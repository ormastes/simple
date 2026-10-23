# Tree RSS floor caps the Stage 2 native-build on a 128 GB host (exit 88)

Date: 2026-10-23
Host: Windows (gnu lane, MinGW UCRT), 128 GB RAM (134,094,232 KiB total), 80 threads
Lane: release_phase3 bootstrap, stage2 native-build, 16 workers

## Observation

The stage2 native-build was killed by the process-tree RSS watchdog with
exit 88 (`stage2-rss-cap-exceeded`), although the real peak was about 10 GB
with 69 GB free. The policy log line:

```
process-tree RSS policy: cap 5859375 KiB (source: default, bound: floor, workers: 16 ... host RAM: 134094232 KiB ... available: 0 via unknown)
```

The cap is the 5,859,375 KiB floor (5.59 GiB) at 16 workers.

## Root cause

`bootstrap_tree_rss_phase_cap_kib` in `scripts/bootstrap/lib/tree-rss-policy.shs`
(~line 390) sizes the stage2 native-build cap at the floor. The floor is a
small-host lower bound, but on a large host it becomes the effective ceiling,
the same failure class as the compiler-tests phase fixed on 2026-10-16.
That fix priced only the Stage 2 compiler-tests phase by host fraction; the
native-build phase still resolves to the floor.

Second defect visible in the same line: `available: 0 via unknown`.
Free-memory detection fails on Windows Git Bash, so the policy has no
available-memory input.

## WORKAROUND

`SIMPLE_BOOTSTRAP_RSS_CAP_MODE=monitor` (watchdog records, does not kill).

## Suggested direction

- Price the stage2 native-build phase by host fraction clamped to
  [floor, jobs-scaled ceiling], as done for stage2 compiler-tests.
- Make free-memory detection work under Windows Git Bash (or report it as an
  explicit failure rather than `0 via unknown`).

## Related

- `doc/08_tracking/bug/tree_rss_floor_kills_stage2_compiler_tests_on_large_hosts_2026-10-15.md`
