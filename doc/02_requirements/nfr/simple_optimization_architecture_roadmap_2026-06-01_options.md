# Simple Optimization Architecture Roadmap NFR Options

Date: 2026-06-01

Scope: non-functional requirements for the persistent `.sprof` lane.
These are options only. Final NFRs require user selection.

## Option 1: Conservative Safety Gate

Targets:
- Disabled profiling adds no hot-path filesystem reads or writes.
- Corrupt, stale, or incompatible profile records are ignored with diagnostics.
- Profile data never bypasses typed-MIR and safe-deoptimization facts.
- `doc/06_spec` executable spec count remains `0`.

Pros:
- Lowest production risk.
- Clear safety story for early `.sprof` adoption.

Cons:
- Does not set strict startup or profile-load latency targets.
- May delay performance wins until later instrumentation exists.

Effort: Small.

## Option 2: Measured Startup and Hot-Request Budget

Targets:
- Warm startup profile loading adds less than 5% over baseline for representative
  compiler/interpreter fixtures.
- Hot request handlers do not reread `.sprof`, shell out, or perform full-tree
  scans.
- Max RSS increase from loaded profile data is reported for realistic fixtures.
- Merge/load benchmarks are recorded before claiming speedups.

Pros:
- Directly matches the roadmap's performance-sensitive tooling rules.
- Prevents profile loading from becoming a hidden startup tax.

Cons:
- Requires representative fixtures and benchmark recording before implementation
  can be called complete.
- More verification work for each profile-schema change.

Effort: Medium.

## Option 3: Release-Grade Profile Durability

Targets:
- Profile writes are atomic or append-safe.
- Interrupted writes preserve the previous valid profile.
- Version mismatch and migration reports are deterministic.
- Profile compatibility behavior is covered by system tests and generated
  manuals.

Pros:
- Strongest persistence and migration guarantees.
- Best fit if `.sprof` is expected to survive across releases.

Cons:
- Larger implementation and test matrix.
- Slower to land than a schema-first or hotspot-only slice.

Effort: Large.

## Selection Needed

Choose one NFR option before final NFRs are written. Unchosen options should be
deleted rather than archived.
