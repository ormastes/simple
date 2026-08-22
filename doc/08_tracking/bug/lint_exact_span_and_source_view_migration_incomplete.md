# Lint exact-span and shared source-view migration is incomplete

## Status

Open. Standalone and query lint now reuse one line view and indexed fallback locations
for collection-function and wildcard-export diagnostics, but the migration is incomplete.

## Remaining gaps

- Parsed warning producers still discard causal AST spans, so compatibility projections
  report a function declaration or first wildcard declaration instead of the expression.
- GC-boundary query diagnostics now reuse indexed imports and first-declaration lines;
  exact parser spans are still not carried by the compatibility warning record.
- Some text-only lint families retain their own scans until matching semantics can move
  into the shared typed fact collector.
- Standalone lint still parses when no validated parsed revision is supplied; compiler and
  LSP callers should use the parsed-revision bridge.

## Completion condition

Warning records carry exact producer spans through typed HIR/AST projections; all fallback
families consume one immutable source index; high-cardinality fixtures preserve diagnostic
order, severity, count, and location without warning-by-line rescans; representative warm
latency and allocation measurements show no regression.

Missing spans remain explicit fallbacks. They must never become proof of typed semantics,
purity, alias safety, or transformation legality.
