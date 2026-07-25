# GETPIVOTDATA ignores its data_field argument (opus review follow-up)

**Date:** 2026-07-04
**Severity:** medium
**Status:** RESOLVED (triage-confirmed 2026-07-17: selector lane reproduced fix in current source via bootstrap-seed run + git log -S)

## Symptom

`=GETPIVOTDATA("NoSuchField", E1)` returns the pivot's grand total (e.g.
100) instead of failing. The data_field argument is parsed but never
validated against the pivot's data-field header; Excel returns #REF for an
unknown field.

## Where

`_eval_getpivotdata` in src/app/office/sheets/formula.spl — add a check
that data_field (quote-stripped, case-insensitive) matches the pivot
region's value-column header before any lookup; unknown → ErrorVal.

## Also (spec quality, same review)

The spec's inline pivot-render helper maps only columns E-H (`else: "H"`),
so pivots wider than 4 columns clobber the last column. Current tests only
exercise column-A/grand-total paths, so they pass legitimately, but
coverage of intersections beyond the first value column is blocked by the
spec helper, not the implementation. Extend the helper's column map and add
a second-column intersection case when lifting this.

Source: opus review of the FORECAST.ETS/GETPIVOTDATA batch (LANDABLE with
follow-ups), 2026-07-04.
