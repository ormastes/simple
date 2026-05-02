# todo_parser_spec_example_scan_escape

Date: 2026-04-22
TODO rows: 147, 148
Status: fixed

## Research

Rows 147 and 148 were not real TODO/FIXME work items. They came from the format example in `test/unit/app/tooling/todo_parser_spec.spl`, where literal `TODO:` and `FIXME:` lines used placeholder fields (`area`, `priority`, `description`, `issue`). The scanner treated those examples as real rows, producing malformed priority counts.

## Plan

Keep the format documentation but rewrite the example so it no longer matches the scanner's real TODO/FIXME pattern.

## Fix

Collapsed the two literal examples into one placeholder line using `<TODO|FIXME>`. This preserves the documented shape while preventing the example from being indexed as actionable work.

While verifying the touched spec, current SPipe lint also flagged legacy `expect expr == value` assertions as empty examples. Converted those assertions to matcher form so the file now passes lint.

## Verification

- `bin/simple lint test/unit/app/tooling/todo_parser_spec.spl`
- `timeout 120s bin/simple test test/unit/app/tooling/todo_parser_spec.spl`
- `perl` row-count check against `doc/08_tracking/todo/todo_db.sdn`
