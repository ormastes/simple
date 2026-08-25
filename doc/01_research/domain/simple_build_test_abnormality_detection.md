# Domain Research: Build/Test Abnormality Detection

This companion records the external techniques selected in the user-provided research specification. Repository-specific validation is in `doc/01_research/local/simple_build_test_abnormality_detection.md`.

## Selected prior art

- Linux cgroup v2 provides hierarchical `memory.current/peak/events`, CPU statistics, and PID controls for a complete descendant scope. A cgroup charge is not RSS and must retain its own field name. Reference: Linux kernel cgroup v2 administration documentation.
- Windows Job Objects provide kill-on-close lifetime ownership, aggregate accounting, active-process limits, and job memory limits. Reference: Microsoft Win32 Job Objects and `JOBOBJECT_*_LIMIT_INFORMATION` documentation.
- POSIX `wait4`/`rusage` provides exact reaped direct-child CPU and maximum-resident evidence. It is not descendant aggregation; `ru_maxrss` units differ between Linux and macOS.
- rustc-perf separates check/debug/opt and full/incremental scenarios; Cargo timings exposes compilation units/concurrency/dependencies; Bazel profiles structured spans and critical paths; Clang/GCC expose hierarchical phase/pass timing and allocation/resource statistics.
- TypeScript extended diagnostics demonstrates work counters (files, lines, nodes, types, instantiations, caches, memory) that explain a timing delta rather than merely reporting it.
- LLVM LNT’s machine/subject/metric identity, Go benchstat’s repeated paired comparisons, and Criterion/Google Benchmark distribution-based decisions support cohort-safe robust comparison.

## Statistical choice

Use paired base/candidate execution on the same runner where possible and compare medians. A regression must exceed a subject-specific absolute floor, a relative floor, and a robust MAD noise floor. Confirmation is required for failure. Retain outliers and tail metrics; use consecutive-shift/EWMA/CUSUM state only for gradual drift, not baseline promotion.

## Safety choice

Resource class and timeout are orthogonal. Hard limits protect the executor even for a new cohort with no approved baseline. Historical evidence may recommend tighter declared budgets but cannot loosen them. Exit status alone is insufficient causal evidence because signals and external termination share encoded statuses.

## Applicability to Simple

Adopt the measurement/accounting semantics, scenario separation, spans, work counters, identity, paired robust comparison, and explicit promotion. Do not import tool-specific storage formats or create a profiler-only execution path; normal build/test commands and `simple perf` operations must share the same evidence model.
