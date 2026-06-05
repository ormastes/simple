# Low Dependency UI dynSMF NFR Options

Date: 2026-06-05

No final NFRs are selected yet.

## Option NFR-A: Conservative Dependency Gate

Description: Add static import closure checks for TUI, GUI base, HTML widget,
CSS implementation, and dynSMF manifests. Fail if forbidden implementation
modules appear in a base lane.

Pros:

- Cheap and deterministic.
- Catches dependency regressions before runtime tests.

Cons:

- Static checks do not prove runtime lazy loading.
- Requires maintenance when modules move.

Effort: Low-medium.

## Option NFR-B: Runtime Load Evidence Gate

Description: Add runtime evidence that records which dynSMF libraries loaded,
which were skipped by arg/env, and which were unloaded/reloaded in a session.

Pros:

- Proves actual loader behavior.
- Supports performance and memory assertions later.

Cons:

- Needs stable evidence format and platform-aware tests.
- Requires careful negative assertions to avoid false greens.

Effort: Medium.

## Option NFR-C: Startup/RSS Budget Gate

Description: Track cold startup time, warm load latency, and max RSS for base
TUI, base GUI, HTML widget, and dynSMF default/opt-out startup paths.

Pros:

- Aligns directly with dependency minimization goals.
- Prevents dynSMF autoload from hiding startup bloat.

Cons:

- More sensitive to host noise.
- Needs representative fixtures and repeat counts.

Effort: Medium-high.

## Recommended Selection

Select NFR-A and NFR-B for the first implementation tranche. Add NFR-C once the
thin vertical slice is stable enough for meaningful perf baselines.
