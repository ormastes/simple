<!-- codex-design -->
# Stage4 re-export resolver options

## Option A — snapshot-owned resolver cache (recommended)

Introduce a `ReexportResolverCache` owned by `ModuleSurfacesByName` (or the
driver context that owns its immutable generation). Key completed root results
by `(snapshot_generation, facade_name, wanted)`, and inject that cache into all
HIR lowering instances. Keep `reexport_active` local to one lookup.

- Pros: deterministic across module/lowering boundaries; explicit
  invalidation; eliminates repeated wildcard scans for both hits and misses.
- Cons: touches surface/driver construction and cache plumbing.
- Effort: medium.

## Option B — per-lowering bounded cache only

Retain the current memo and add an explicit bounded negative cache per
`HirLowering`, clearing it on every module transition.

- Pros: small localized patch; no surface API changes.
- Cons: does not eliminate cross-module repeated façade scans, so it cannot
  meet the R6 Stage4 performance failure.
- Effort: low.

## Option C — precompute façade export origins

At `ModuleSurfaceBuilder.finish()`, materialize a direct mapping from every
facade export to its declaring module and make HIR lookup an O(1) table read.

- Pros: strongest steady-state performance and simple HIR hot path.
- Cons: complex alias/glob/cycle semantics must be fully represented during
  construction; higher risk of changing diagnostics and partial-module use.
- Effort: high.
