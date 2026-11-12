# `split_sdn_row` ignored backslash escapes inside quotes (2026-11-12)

- **Status:** FIXED 2026-11-12 on release/1.0.0 (Windows phase-1 bug sweep)
- **Severity:** P2 (table-shape oracle divergence; parse fail-closed data loss)
- **Area:** `src/lib/nogc_sync_mut/database/core.spl` (`split_sdn_row`)

## Symptom

`split_sdn_row` toggled quote state on every `"` without honoring backslash
escapes. A quoted field containing `\"` (e.g. an escaped quote inside a bug
title) therefore ended the quoted region early, and commas in the remainder
were counted as field separators. The canonical field counter
(`scripts/check/check-bug-db-table-shape.shs`, which honors `\"` inside
quotes) and the Simple-side parser disagreed:

- `bug_db_table_shape_spec.spl` counted
  `coverage_test_flag_times_out_and_mcdc_no_probes_windows_2026-11-03` as an
  11-field `bugs_active` row (10 per the awk counter).

## Fix

`split_sdn_row` now consumes `\<char>` as an escaped pair inside quotes (the
escaped character is field content and cannot toggle quote state or act as a
separator), matching the awk counter's semantics exactly. Evidence:
`bug_db_table_shape_spec.spl` 1/1 and `bug_snapshot_crc_spec.spl` 7/7 on the
fresh Windows seed (build-commit `8289600e9cb`).

## Related data repair (same sweep)

`doc/08_tracking/bug/bug_db.sdn` contained two leftover literal `$row`
template lines inside `bugs_active` (lines 4348 and 5815 pre-fix). They are
1-field rows in a 10-column table, so `SdnTable.parse` fail-closed rejected
the ENTIRE table, surfacing downstream as "canonical bug database has no bug
table" in `workaround_bug_snapshot`. Both lines were removed and the file was
re-sealed (`reseal-sdn-crc32.shs` → `bug_db.xxh3_87fccae4172791e3.csm`).
