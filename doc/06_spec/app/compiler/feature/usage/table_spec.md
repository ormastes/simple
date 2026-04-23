# Table (DataFrame) Specification

Table/DataFrame-like data structure for tabular data:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2250-2260 |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/feature/usage/table_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Table/DataFrame-like data structure for tabular data:
- Column-based storage with typed columns
- SQL-like operations (select, where, join)
- Aggregation and grouping
- Statistical operations

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/table/result.json` |

## Scenarios

- creates table from column list
- creates table from dict of arrays
- gets column via get()
- returns nil for missing column
- sums numeric column
- computes mean
- finds minimum
- finds maximum
- computes standard deviation
- filters by predicate
- chains multiple filters
- selects specific columns
- drops specific columns
- sorts ascending by column
- sorts descending
- groups by single column
- computes sum per group
- supports multiple aggregations
- joins on common column
- adds new column
- adds column from computation
- chains filter, select, and aggregate
- computes department statistics
- gets unique values
- counts value occurrences
