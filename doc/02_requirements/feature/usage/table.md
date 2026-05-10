# Table (DataFrame) Specification
*Source:* `test/feature/usage/table_spec.spl`
**Feature IDs:** #2250-2260  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview




Table/DataFrame-like data structure for tabular data:
- Column-based storage with typed columns
- SQL-like operations (select, where, join)
- Aggregation and grouping
- Statistical operations

## Feature: Table Construction

Creating tables from various sources.

### Scenario: from columns

| # | Example | Status |
|---|---------|--------|
| 1 | creates table from column list | pass |

**Example:** creates table from column list
    Given val col1 = Column(name: "x", data: [1, 2, 3])
    Given val col2 = Column(name: "y", data: [4, 5, 6])
    Given val table = table_from_columns([col1, col2])
    Then  expect(table.num_rows).to_equal(3)
    Then  expect(table.column_names.len()).to_equal(2)

### Scenario: from dictionary

| # | Example | Status |
|---|---------|--------|
| 1 | creates table from dict of arrays | pass |

**Example:** creates table from dict of arrays
    Given var data = {}
    Given val table = table_from_dict(data)
    Then  expect(table.num_rows).to_equal(3)
    Then  expect(table.column_names.len()).to_equal(2)

## Feature: Column Access

Accessing table columns.

### Scenario: by name

| # | Example | Status |
|---|---------|--------|
| 1 | gets column via get() | pass |
| 2 | returns nil for missing column | pass |

**Example:** gets column via get()
    Given var data = {}
    Given val table = table_from_dict(data)
    Given val col_opt = table_get(table, "x")
    Then  expect(col_opt.?).to_equal(true)

**Example:** returns nil for missing column
    Given val table = table_empty()
    Given val col_opt = table_get(table, "missing")
    Then  expect(col_opt.?).to_equal(false)

## Feature: Column Reductions

Statistical operations on columns.

### Scenario: sum

| # | Example | Status |
|---|---------|--------|
| 1 | sums numeric column | pass |

**Example:** sums numeric column
    Given val col = Column(name: "x", data: [1, 2, 3, 4])
    Given val total = column_sum(col)
    Then  expect(total).to_equal(10.0)

### Scenario: mean

| # | Example | Status |
|---|---------|--------|
| 1 | computes mean | pass |

**Example:** computes mean
    Given val col = Column(name: "x", data: [2, 4, 6, 8])
    Given val avg = column_mean(col)
    Then  expect(avg).to_equal(5.0)

### Scenario: min/max

| # | Example | Status |
|---|---------|--------|
| 1 | finds minimum | pass |
| 2 | finds maximum | pass |

**Example:** finds minimum
    Given val col = Column(name: "x", data: [5, 2, 8, 1, 9])
    Given val minimum = column_min(col)
    Then  expect(minimum).to_equal(1)

**Example:** finds maximum
    Given val col = Column(name: "x", data: [5, 2, 8, 1, 9])
    Given val maximum = column_max(col)
    Then  expect(maximum).to_equal(9)

### Scenario: std/var

| # | Example | Status |
|---|---------|--------|
| 1 | computes standard deviation | pass |

**Example:** computes standard deviation
    Given val col = Column(name: "x", data: [2, 4, 6, 8])
    Given val std = column_std_dev(col)
    Then  expect(std > 2.0).to_equal(true)
    Then  expect(std < 2.5).to_equal(true)

## Feature: Filtering

Filtering table rows.

### Scenario: where

| # | Example | Status |
|---|---------|--------|
| 1 | filters by predicate | pass |
| 2 | chains multiple filters | pass |

**Example:** filters by predicate
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_where(table1, fn(row): row["x"] > 2)
    Then  expect(table2.num_rows).to_equal(3)

**Example:** chains multiple filters
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_where(table1, fn(row): row["x"] > 2)
    Given val table3 = table_where(table2, fn(row): row["y"] < 50)
    Then  expect(table3.num_rows).to_equal(2)

## Feature: Selection

Selecting and dropping columns.

### Scenario: select

| # | Example | Status |
|---|---------|--------|
| 1 | selects specific columns | pass |

**Example:** selects specific columns
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_select(table1, ["a", "c"])
    Then  expect(table2.column_names.len()).to_equal(2)

### Scenario: drop

| # | Example | Status |
|---|---------|--------|
| 1 | drops specific columns | pass |

**Example:** drops specific columns
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_drop(table1, ["b"])
    Then  expect(table2.column_names.len()).to_equal(2)

## Feature: Sorting

Sorting table rows.

### Scenario: sort_by

| # | Example | Status |
|---|---------|--------|
| 1 | sorts ascending by column | pass |
| 2 | sorts descending | pass |

**Example:** sorts ascending by column
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_sort_by(table1, "x", true)
    Given val x_col = table_get(table2, "x")
    Then  expect(x_col.?).to_equal(true)

**Example:** sorts descending
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_sort_by(table1, "x", false)
    Given val x_col = table_get(table2, "x")
    Then  expect(x_col.?).to_equal(true)

## Feature: Grouping and Aggregation

Grouping rows and computing aggregates.

### Scenario: group_by

| # | Example | Status |
|---|---------|--------|
| 1 | groups by single column | pass |
| 2 | computes sum per group | pass |

**Example:** groups by single column
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_group_by(table1, "category", "value", "sum")
    Then  expect(table2.num_rows).to_equal(2)

**Example:** computes sum per group
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_group_by(table1, "category", "value", "sum")
    Then  expect(table2.num_rows).to_equal(2)

### Scenario: aggregation functions

| # | Example | Status |
|---|---------|--------|
| 1 | supports multiple aggregations | pass |

**Example:** supports multiple aggregations
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val sum_table = table_group_by(table1, "x", "y", "sum")
    Given val mean_table = table_group_by(table1, "x", "y", "mean")
    Then  expect(sum_table.num_rows).to_equal(1)
    Then  expect(mean_table.num_rows).to_equal(1)

## Feature: Joins

Joining tables together.

### Scenario: inner join

| # | Example | Status |
|---|---------|--------|
| 1 | joins on common column | pass |

**Example:** joins on common column
    Given var left_data = {}
    Given val left_table = table_from_dict(left_data)
    Given var right_data = {}
    Given val right_table = table_from_dict(right_data)
    Given val joined = table_inner_join(left_table, right_table, "id")
    Then  expect(joined.num_rows).to_equal(2)

## Feature: Computed Columns

Adding computed columns.

### Scenario: with_column

| # | Example | Status |
|---|---------|--------|
| 1 | adds new column | pass |

**Example:** adds new column
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_with_column(table1, "y", [10, 20, 30])
    Then  expect(table2.column_names.len()).to_equal(2)

### Scenario: with_computed

| # | Example | Status |
|---|---------|--------|
| 1 | adds column from computation | pass |

**Example:** adds column from computation
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_with_computed(table1, "x2", fn(row): row["x"] * 2)
    Then  expect(table2.column_names.len()).to_equal(2)

## Feature: Chained Operations

Fluent interface with method chaining.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | chains filter, select, and aggregate | pass |
| 2 | computes department statistics | pass |

**Example:** chains filter, select, and aggregate
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_where(table1, fn(row): row["x"] > 2)
    Given val table3 = table_select(table2, ["x"])
    Then  expect(table3.num_rows).to_equal(3)
    Then  expect(table3.column_names.len()).to_equal(1)

**Example:** computes department statistics
    Given var data = {}
    Given val table1 = table_from_dict(data)
    Given val table2 = table_group_by(table1, "dept", "salary", "mean")
    Then  expect(table2.num_rows).to_equal(2)

## Feature: Column Utilities

Column-level operations.

### Scenario: unique

| # | Example | Status |
|---|---------|--------|
| 1 | gets unique values | pass |

**Example:** gets unique values
    Given val col = Column(name: "x", data: [1, 2, 2, 3, 3, 3])
    Given val uniq = column_unique(col)
    Then  expect(uniq.len()).to_equal(3)

### Scenario: value_counts

| # | Example | Status |
|---|---------|--------|
| 1 | counts value occurrences | pass |

**Example:** counts value occurrences
    Given val col = Column(name: "x", data: [1, 2, 2, 3, 3, 3])
    Given val counts = column_value_counts(col)
    Then  expect(counts.len()).to_equal(3)


