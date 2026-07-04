<!-- codex-research -->
# GUI Lib macOS + SimpleOS QEMU ARM64 Perf Feature Options

## Option A: Evidence-First Validation Harness

Description: Consolidate existing scripts/specs into one operator flow that checks macOS host GUI, Metal readback, QEMU ARM64 readiness, QMP capture, and capture diff reporting.

Pros: Lowest risk; uses existing surfaces; quickly exposes missing prerequisites and drawing inconsistency bugs.

Cons: Does not itself optimize slow pure-Simple paths; may leave perf gaps as follow-up implementation tasks.

Effort: M, about 4-8 files.

## Option B: Validation Harness + Pure-Simple Hot Path Optimization

Description: Do Option A, then optimize the measured pure-Simple Engine2D/WM hot paths that fail selected NFRs.

Pros: Directly targets the user's performance concern; keeps optimization evidence-driven.

Cons: Higher risk; requires before/after benchmarks and may touch shared render APIs.

Effort: L, about 8-16 files.

## Option C: Full Cross-Target GUI Consistency Gate

Description: Build a release-blocking gate covering host GUI, browser/web render, SimpleOS QEMU ARM64, QMP screenshots, baseline diff reports, and perf thresholds.

Pros: Strongest long-term regression prevention; produces durable CI-style evidence.

Cons: Highest setup cost; QEMU/Metal availability may make it hard to run everywhere without capability-aware skips.

Effort: XL, about 16-30 files.

## User Decision Needed

Select one feature option before final requirements are written. Unselected option files should be deleted after selection.
