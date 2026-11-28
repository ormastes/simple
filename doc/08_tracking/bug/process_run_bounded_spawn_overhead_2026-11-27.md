# process_run_bounded / process_run_bounded_bytes: ~11 ms fixed cost per child

- Date: 2026-11-27
- Status: verification-pending (fix: backoff poll in `finish_child_output_bounded_mode`)
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

## Fix (2026-11-28)

The seed runtime's bounded wait loop (`env_process.rs`,
`finish_child_output_bounded_mode`) slept a fixed 10 ms per iteration. Its
stdout and stderr reader threads start inside that loop, so the first poll
always missed and every child paid at least 10 ms. The poll interval now backs
off from 100 us to 10 ms.

Measured with the unit test `bounded_wait_adds_no_fixed_poll_quantum` on
Windows, timing only the wait on a child that has already exited, 9 samples:

| | median wait latency |
|---|---|
| fixed 10 ms (before) | 10.94 ms |
| backoff (after) | 0.97 ms |

Not yet re-measured: the Linux 100-child loop above. The WSL distro is
read-only on the measuring host.
