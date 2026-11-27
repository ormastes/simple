# process_run_bounded / process_run_bounded_bytes: ~11 ms fixed cost per child

- Date: 2026-11-27
- Status: open (perf)
- Area: `src/lib/nogc_sync_mut/io/process_ops.spl` (`process_run_bounded`,
  `process_run_bounded_bytes`) and their native runtime capture providers
- Found by: the matched-app benchmark twin (`src/app/item5_perf/main.spl`) parity run

## Measurement (WSL ubuntu-p2, seed built from release/1.0.0 on 2026-11-27, `bin/simple run`)

| loop of 100 children | wall |
|---|---|
| `process_run_bounded_bytes("env", ["-C", "/dev/shm", "true"], …)` | 1131 ms |
| `process_run_bounded("true", [], …)` | 1315 ms |
| `/bin/sh` loop of `env -C /dev/shm true` | 222 ms |

That is about 11-13 ms per child in the Simple runtime against about 2.2 ms from
the shell. The size of the gap suggests a fixed poll or sleep interval in the
bounded-capture wait loop rather than real spawn work.

## Impact

The pure-Simple twin of `run-item5-matched-app-performance.py` spawns one
watchdog child per sample. On the synthetic parity fixture (180 samples, trivial
apps) it takes 5.7 s against 1.5 s for Python. Startup is about 1.3 s of that,
and the rest is mostly this per-child cost. The benchmark's measured values (the
apps' own `ns` fields, watchdog RSS) are outside that window and are byte-identical
to Python's. Only the whole-cohort wall time and the
`--cohort-timeout-seconds` budget absorb the extra cost: about 2 s over a
100-pair release cohort. Every bounded-capture caller pays it too.

## Next step

Find the wait/poll interval in the native bounded capture provider and replace it
with a blocking wait (pidfd/poll on the pipes plus waitpid). Re-measure with the
loop above; the target is under 3 ms per child.
