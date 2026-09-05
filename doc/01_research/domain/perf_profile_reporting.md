# Performance Profile Reporting Domain Research

**Date:** 2026-06-06

## Sources

- Google Benchmark user guide: https://google.github.io/benchmark/user_guide.html
- Criterion.rs analysis process: https://bheisler.github.io/criterion.rs/book/analysis.html
- Criterion.rs command output: https://bheisler.github.io/criterion.rs/book/user_guide/command_line_output.html
- pyperf run benchmark guide: https://pyperf.readthedocs.io/en/latest/run_benchmark.html
- pyperf system tuning guide: https://pyperf.readthedocs.io/en/stable/system.html

## Relevant Practices

- Benchmark reports need enough environment metadata to reproduce the run: host, OS/CPU, command, workload knobs, and output path.
- Warmup and measurement phases should be distinguished. Criterion.rs and pyperf both treat warmup separately from measured samples; Google Benchmark also exposes controls around iterations, repetitions, and wall-clock timing.
- Reports should explicitly classify unavailable or failed lanes. Missing dependencies should not be interpreted as a winning performance comparison.
- Small timing deltas need repeated runs and host-noise context. pyperf emphasizes system tuning to reduce jitter, and Criterion.rs reports outliers because they weaken the reliability of averages.
- Startup timing and steady-state throughput are different metrics. They should appear as separate sections so startup overhead is not blended with warmed loop throughput.

## Repo Implications

- The language profile should label outer-process interpreter/SMF timing separately from in-process warm timing.
- The GUI profile should record backend status and max RSS, but rows that only initialize a backend must not be described as valid frame-time evidence.
- TUI startup speed should remain in the startup-size audit and be linked from the GUI/language profile reports instead of being silently conflated with GUI backend rendering.
