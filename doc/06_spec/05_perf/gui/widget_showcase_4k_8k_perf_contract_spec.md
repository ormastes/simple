# GUI Widget Showcase 4K/8K Perf Contract

## Purpose

This manual spec mirrors
`test/05_perf/gui/widget_showcase_4k_8k_perf_contract_spec.spl`.
It protects the retained 4K/8K GUI widget showcase performance evidence
contract without running the expensive benchmark on headless hosts.

## Run

```sh
SIMPLE_LIB=src bin/simple test test/05_perf/gui/widget_showcase_4k_8k_perf_contract_spec.spl --mode=interpreter --clean
```

## Completion Criteria

- The checker rejects Rust seed Simple binaries.
- The checker prefers self-hosted Simple binaries and only uses PATH Simple when
  explicitly opted in.
- 4K evidence remains tied to 3840x2160 and 200fps.
- 8K evidence remains tied to 7680x4320 and 200fps.
- Evidence includes FPS, p50/p95 frame timing, checksum/readback, RSS budget,
  retained render mode, redraw count, log file status, timing-log status, and
  source revision rows.
- The generated retained alias is scanned before native-build and fails with
  `alias-raw-rt-forbidden` if raw `rt_*` calls enter the alias source.
- In plan-only mode, both 4K and 8K alias generation must report
  `*_alias_raw_rt_count=0` without native build or GUI execution.
- Passing this spec is source preparation only. It does not produce a new 4K or
  8K performance measurement.
