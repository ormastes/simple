<!-- codex-plan -->
# Science Math DataFrame Compatibility Manifest

**Date:** 2026-05-05
**Status:** Phase D compatibility manifest.
**Requirements:** `REQ-SCILIB-D-001` through `REQ-SCILIB-D-004`.
**Source:** `src/lib/nogc_sync_mut/df/mod.spl`, `src/lib/nogc_async_mut/df/`
**Specs:** `test/feature/scilib/df_*_spec.spl`

## Compatibility Position

`std.df` is a narrow, typed table library with pandas-style workflow names where they are useful. It is not a full pandas replacement. Phase D expands only from this manifest so new methods solve concrete workflows instead of chasing breadth.

## v1 Complete Surface

| Area | Public behavior | Evidence |
| --- | --- | --- |
| Construction | `Series.from_values`, masked F64/I64 series, `DataFrame.from_columns`, `DataFrame.from_rows` | `df_construction_spec.spl` |
| Column access | `columns`, `col`, `assign`, `drop`, `rename`, `dtypes`, `astype_i64_to_f64` | `df_column_ops_spec.spl` |
| Row access | `row`, `take` | `df_indexing_spec.spl` |
| Filtering | Boolean mask filtering with dtype preservation | `df_filter_spec.spl` |
| Head/tail | Bounded first/last row selection | `df_head_tail_spec.spl` |
| Sorting | `sort_values` for numeric keys | `df_sort_values_spec.spl` |
| Concat | Row concat and column concat | `df_concat_spec.spl` |
| Joins | Inner, left, right, and outer numeric-key merge/join | `df_merge_spec.spl` |
| Groupby | Numeric-key grouped sum and mean | `df_groupby_spec.spl` |
| Missing values | Per-series missing masks, row materialization as `DfValue.Na`, join/concat/CSV preservation | `df_csv_text_spec.spl`, `df_merge_spec.spl` |
| CSV/text I/O | Numeric CSV parse/export with blank cells as missing, integer-column import as I64, and decimal-preserving F64 export | `df_csv_text_spec.spl` |
| Async facade | `nogc_async_mut.df` re-export of sync DataFrame surface, including reshape-lite helpers | `df_async_facade_spec.spl` |
| Reshape-lite | `melt_numeric` wide-to-long reshape for one id column and numeric value columns | `df_melt_spec.spl` |
| Pivot-lite | `pivot_sum` long-to-wide numeric aggregation with Int64 column keys and Float64 values | `df_pivot_spec.spl` |
| Datetime-lite | `iso_date_series` and `parse_iso_date_days` parse ISO `YYYY-MM-DD` values to Int64 day offsets from 1970-01-01 | `df_datetime_categorical_spec.spl` |
| Categorical-lite | `categorical_encode` maps first-seen `Symbol` labels to Int64 codes and returns the label table separately | `df_datetime_categorical_spec.spl` |

## Phase D Expansion Queue

| Priority | Area | Acceptance boundary |
| --- | --- | --- |
| D1 | Compatibility manifest and traceability | This file exists and each DataFrame spec maps to a manifest row. |
| D2 | Reshape-lite | Complete: `melt_numeric` supports one id column, numeric value columns, Int64 variable ordinal, and Float64 value output. No multi-index, no arbitrary object dtype. |
| D3 | Pivot-lite | Complete: `pivot_sum` supports one numeric index key, one Int64 column key, explicit sum aggregation, and Float64 value output. |
| D4 | Datetime ingestion | Complete: explicit ISO date ingestion stores day offsets as Int64 values. No timezone, timestamp, frequency, or calendar-index semantics. |
| D5 | Categorical labels | Complete: explicit first-seen `Symbol` label encoding stores category codes as Int64 and returns labels separately. No object dtype or implicit text columns. |

## Non-Goals

- Full pandas indexing semantics, including multi-index.
- Object dtype, arbitrary text columns, or mixed-type columns beyond explicit `DfValue` row materialization.
- Implicit dtype widening beyond documented conversions.
- DataFrame operations inside `math{}` or `m{}`.
- Silent missing-value coercions.

## Verification Gate

Phase D changes must update this manifest and add or extend a `test/feature/scilib/df_*_spec.spl` file with:

- at least one successful workflow assertion;
- at least one invalid-input assertion where invalid input is possible;
- no `skip()`, `pass_todo`, placeholder assertions, or TODO-only bodies;
- interpreter-mode compatibility under `SIMPLE_BLAS_BACKEND=mock`.
