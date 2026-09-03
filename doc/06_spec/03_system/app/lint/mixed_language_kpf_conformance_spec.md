# Mixed-Language KPF Lint Conformance

This executable scenario proves that one lint composition can combine a native Simple result with bounded Rust Cargo/Clippy and C++ clang-tidy worker results without treating missing or unauthoritative provider evidence as clean.

## Scenarios

1. Execute all three language lanes and require exact aggregate unit, rule, phase, and diagnostic counts.
2. Remove the required C++ provider result and require a non-clean `NotAnalyzed` verdict with explicit skipped coverage.
3. Strip the C++ provider's authority evidence and require a `Failed` verdict.

## Evidence

```text
<runtime> test test/03_system/app/lint/mixed_language_kpf_conformance_spec.spl --mode=interpreter
```

The 2026-09-03 focused run passed all three scenarios on `/Users/ormastes/simple/bin/release/macos-arm64/simple`. Broader `check src/lib` and `check src/app/lint` qualification could not complete because that external runtime returned the already identified launcher status `-1`; this is not counted as a pass.
