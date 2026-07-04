<!-- codex-research -->
# GUI Lib macOS + SimpleOS QEMU ARM64 Perf NFR Options

## Option 1: Sanity Baseline

Description: Require host sanity, Metal readback, QEMU readiness, and non-empty capture evidence; record perf numbers without hard thresholds.

Pros: Reliable on varied developer machines; good first pass for bug discovery.

Cons: Does not prevent performance regressions.

Effort: S, about 2-4 files.

## Option 2: Developer-Machine Perf Guard

Description: Require median frame/render times and capture diff thresholds on a named macOS host profile, with capability-aware skips for absent QMP/Metal.

Pros: Meaningful local guard; catches regressions while still runnable by developers.

Cons: Machine-specific thresholds need calibration and periodic refresh.

Effort: M, about 4-8 files.

## Option 3: Strict Release Gate

Description: Require HVF-backed QEMU ARM64, Metal readback, QMP screendump, zero deterministic VM pixel mismatches, bounded host diff ratio, and max frame-time/RSS thresholds.

Pros: Strongest correctness and performance signal.

Cons: Requires stable hardware/software target; can block release if QEMU or capture setup is unavailable.

Effort: L, about 8-14 files.

## User Decision Needed

Select one NFR option before final NFR requirements are written.
