# Table (DataFrame) Specification

**Feature ID:** #2250-2260 | **Category:** Stdlib | **Status:** Implemented

_Source: `test/feature/usage/table_spec.spl`_

---

Table/DataFrame-like data structure for tabular data:
- Column-based storage with typed columns
- SQL-like operations (select, where, join)
- Aggregation and grouping
- Statistical operations

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 25 |

## Test Structure

### Table Construction

#### from columns

- ✅ creates table from column list
#### from dictionary

- ✅ creates table from dict of arrays
### Column Access

#### by name

- ✅ gets column via get()
- ✅ returns nil for missing column
### Column Reductions

#### sum

- ✅ sums numeric column
#### mean

- ✅ computes mean
#### min/max

- ✅ finds minimum
- ✅ finds maximum
#### std/var

- ✅ computes standard deviation
### Filtering

#### where

- ✅ filters by predicate
- ✅ chains multiple filters
### Selection

#### select

- ✅ selects specific columns
#### drop

- ✅ drops specific columns
### Sorting

#### sort_by

- ✅ sorts ascending by column
- ✅ sorts descending
### Grouping and Aggregation

#### group_by

- ✅ groups by single column
- ✅ computes sum per group
#### aggregation functions

- ✅ supports multiple aggregations
### Joins

#### inner join

- ✅ joins on common column
### Computed Columns

#### with_column

- ✅ adds new column
#### with_computed

- ✅ adds column from computation
### Chained Operations

- ✅ chains filter, select, and aggregate
- ✅ computes department statistics
### Column Utilities

#### unique

- ✅ gets unique values
#### value_counts

- ✅ counts value occurrences

