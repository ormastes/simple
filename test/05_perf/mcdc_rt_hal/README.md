# MC/DC and rt(hal) performance evidence

Run `sh test/05_perf/mcdc_rt_hal/run_perf_evidence.shs`. The runner builds all
MC/DC modes from one fixture, warms each process lane once, retains seven
identical samples, records p50 in-process time and peak RSS, checks output
checksums, records executable and `.text` size, obtains allocation evidence via
Heaptrack, and exercises fixed-buffer saturation. It also measures the same
bounded rt(hal) request set for Pure-only, C, Rust, and C+Rust policy lanes.
The analyzer fixture independently doubles E and C and gates each time/RSS
ratio, catching an accidental quadratic pair scan.
Fixture selection is passed through explicit CLI arguments; benchmark leaves
do not read environment variables or invoke processes directly.

The runner is fail-closed: missing GNU time, `size`, Heaptrack, compiler support,
or a foreign comparison route is `BLOCKED`, never a passing zero. Override only
run count/build paths with the documented environment variables in the script;
the retained fixture and thresholds remain versioned in `thresholds.sdn`.

Run `sh test/05_perf/mcdc_rt_hal/run_optimizer_receipts.shs` separately. It
invokes the canonical Pure Simple optimizer once for every path in
`optimizer_inputs.txt` and retains command, revision, source digest, exit code,
and complete output under `build/perf/mcdc_rt_hal/optimizer/`.
