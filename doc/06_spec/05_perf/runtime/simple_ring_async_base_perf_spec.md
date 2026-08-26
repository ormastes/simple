# SimpleRing Async Base Measured Performance

Status: **AUTHORED MIRROR — NOT A PERFORMANCE PASS**

Source: `test/05_perf/runtime/simple_ring_async_base_perf_spec.spl`

## Purpose and audience

This performance scenario is for runtime maintainers selecting future
regression thresholds for the hosted SimpleRing V1 reference provider. It
measures the production ring/provider path; it is not a substitute for a
native-provider or mission-qualified benchmark.

## Preconditions

- Use an admitted pure-Simple self-hosted runtime.
- Retain the runtime path/hash, source revision, host/CPU, build profile, and
  command with the measurement output.
- Do not admit Rust-seed output as Simple performance evidence.

## Operator workflow

1. Measure repeated fixed-capacity ring cycles.
2. Measure repeated all-or-nothing batch cycles.
3. Retain the emitted `simple_ring_perf` rows as the candidate baseline.
4. Select regression thresholds only after comparable repeated runs exist.

## Measurements

Each lane emits wall-clock p50, p99, and p99.9 latency; operations/second;
ring high-water, full-event, batch, and batch-item counters; provider kicks;
caller-clock completion-latency telemetry; and a correctness checksum.

The clock provenance is `std.io_runtime.time_now_unix_micros`. The current
source intentionally contains no hardcoded speed threshold because no admitted
baseline has been retained yet.

## Verification and outcomes

The executable assertions require nonzero execution and throughput, ordered
percentiles, bounded occupancy, exact batch/full/kick/sample counters, and a
nonzero completion checksum. These checks establish harness correctness and
telemetry consistency only.

## Compatibility and limitations

This scenario does not prove steady-state allocation behavior, RSS bounds,
native queue mapping, executor nonblocking behavior, or mission qualification.
Its authored mirror has not been generated or validated by SPipe in this lane,
and therefore must not be reported as a generated-manual PASS.

The one permitted syntax diagnostic was attempted with the deployed binary on
2026-08-26. That binary identified itself as a Rust bootstrap seed and the
check stopped on the pre-existing `dir_list` non-optional-return semantic
error. The benchmark itself was not executed.

## Baseline status

`baseline=needed`; no speed-regression gate is claimed.
