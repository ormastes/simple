# LibreOffice Base Test Plan

## Requirements

- BASE-001 and BASE-002: Existing row count, column index, select, and projection
  scenarios continue to pass.
- BASE-003: Checked insert accepts matching row widths and rejects short or long
  rows without changing the table.
- BASE-004: Filtered counts cover matching, no-match, and missing-column cases.
- BASE-005: Update-by-predicate changes all matching rows and leaves the source
  table unchanged.
- BASE-006: Delete-by-predicate removes all matching rows and leaves remaining
  rows in order.
- BASE-007: Missing-column and no-match edits reject with deterministic reasons
  and unchanged tables.

## Evidence

- Unit spec: `test/01_unit/app/office/base_db_spec.spl`
- IDE catalog system spec:
  `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`
- Generated manuals:
  `doc/06_spec/test/01_unit/app/office/base_db_spec.md`
  `doc/06_spec/test/03_system/app/ide/feature/ide_office_plugin_suite_spec.md`
