<!-- codex-research -->

# Compiler startup dynload and compile-time gate: domain research

Date: 2026-09-01. Primary sources only.

## Applicable practice

- LLVM loads pass plugins explicitly (`-load-pass-plugin`) and registers them
  at typed pipeline extension points; analyses are cached and invalidated by
  the pass manager. This supports Simple's selected-provider attachment and
  typed AOP/backend extension points, rather than eager global discovery:
  [LLVM New Pass Manager](https://llvm.org/docs/NewPassManager.html).
- Clang exposes per-compilation time traces and per-subprocess wall/user/RSS
  reports. Simple should make the same phase/resource receipt available on
  bootstrap, with filenames only in an explicitly verbose trace:
  [Clang Users Manual](https://clang.llvm.org/docs/UsersManual.html).
- LLVM's benchmarking guidance requires high-resolution timing, repeated runs,
  reduced system noise, controlled CPU frequency and avoidance of storage
  variance. It warns that low variance does not eliminate measurement bias:
  [LLVM Benchmarking](https://www.llvm.org/docs/Benchmarking.html).
- Google Benchmark's upstream guide separates warmup from measurement and
  reports mean, median, standard deviation and coefficient of variation over
  repetitions. This supports a robust aggregate and an explicit noise screen,
  not a single wall-clock threshold:
  [Google Benchmark user guide in llvm-project](https://github.com/llvm/llvm-project/blob/main/third-party/benchmark/docs/user_guide.md).
- Rust's Clippy benchmarking uses instruction count because it is more
  reproducible than wall time, and compares the same workload before/after.
  Simple should retain wall time as the user-facing gate but use instructions
  or CPU time as corroborating evidence when available:
  [Clippy benchmarking documentation](https://doc.rust-lang.org/stable/clippy/development/infrastructure/benchmarking.html).
- Clang's `-ftime-trace` guidance recommends narrowing an expensive compilation
  to the entry/function and then using sampling/instrumenting profilers. Simple
  should preserve per-file/per-phase traces so a +10% failure identifies the
  responsible phase rather than triggering blind full-bootstrap retries:
  [Clang performance investigation](https://clang.llvm.org/docs/analyzer/developer-docs/PerformanceInvestigation.html).

## Recommended +10% rule

Use a paired baseline and candidate on the same admitted host profile. Run one
untimed warmup then at least seven alternating `B,C,C,B,...` repetitions per
fixture. Gate each cold/warm/edit lane independently on the median of paired
ratios, corroborated by a 20% trimmed mean. Fail when both aggregates exceed
1.10 and each side's coefficient of variation is at most 5%. If noise exceeds
5%, mark the result `INCONCLUSIVE`, retry once on a quiet dedicated runner, and
never pass it by averaging in unrelated faster fixtures.

Baseline receipts must bind executable and source commit digests, target,
backend, profile, cache schema/state digest, fixture digest, host/kernel/CPU,
core allocation, memory limit, sample vector and phase counters. A changed
machine/profile creates a new baseline; it must not silently bless the current
commit. Also retain absolute budgets, because ratio-only gates tolerate a slow
baseline and become unstable near zero.
