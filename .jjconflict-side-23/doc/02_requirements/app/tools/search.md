# Registry Search Specification
*Source:* `test/03_system/feature/app/search_spec.spl`

## Overview



**Difficulty:** 2/5

## Overview
Tests for the `simple search` command that queries the package listing.

## Key Concepts
- Package listing parsing
- Name and description matching
- Result limiting
- Embedded table search
- BM25-style ranking
- FTS5-compatible API alias

## Behavior

## Package Search
    Tests for searching the registry by name or description.

### When when packages match

- finds packages by name
- finds packages by description
- is case insensitive

### When when no packages match

- returns empty list

### When when limit is applied

- respects result limit

## Embedded Search

The embedded database search surface lives in the pure Simple database engine.
It provides a SQLite-style search API for local tables without requiring an
external SQLite dependency.

### Algorithms

- `Contains` returns rows whose selected text columns contain the query tokens.
- `TermFrequency` ranks matching rows by token frequency.
- `Bm25` ranks matching rows with document length and document frequency
  normalization.

### API Contract

- `PureDatabase.search(table, columns, query, algorithm, limit)` returns ranked
  `PureSearchResult` values with the source row, score, and row index.
- `PureDatabase.bm25_search(table, columns, query, limit)` is the direct BM25
  helper.
- `PureDatabase.fts5_search(table, columns, query, limit)` is a compatibility
  alias for BM25-style ranked search.
- Empty queries and missing tables return empty results rather than crashing.
- Limits are applied after ranking and preserve deterministic ordering for equal
  scores.

