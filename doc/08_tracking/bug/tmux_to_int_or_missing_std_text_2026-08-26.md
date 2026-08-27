# tmux: `to_int_or` imported from `std.text`, which never defined it (2026-08-26)

**Symptom.** `bin/simple test test/01_unit/lib/std/tmux/tmux_api_spec.spl` failed
at load with `semantic: function `to_int_or` not found` (three times, one per
resolution pass) and `error: test-runner: spec failed`; the spec ran 0 examples.
**Cause.** `src/lib/nogc_sync_mut/tmux/mod.spl` declared
`use std.text.{to_int_or}`, but `std.text` (`src/lib/common/text.spl`) exports
only `parse_i64, trim, is_empty, not_empty, contains, escape_json, NL` — the only
`to_int_or` in the tree is a private helper in
`src/lib/nogc_sync_mut/database/feature_utils.spl`, and `text.to_int_or(...)`
is not a runtime method either. **Fix.** Replaced the bad import with
`use std.convert.{try_parse_int}` and a module-local
`fn to_int_or(s: text, default: i64) -> i64: try_parse_int(s) ?? default`, the
same fail-closed shape `feature_utils.spl` already documents (no new public API,
so no new spec). **Verification.** Same command now prints
`SPEC FILE VERDICT ... outcome=OK executed=12 passed=12 failed=0` and
`PASS test/01_unit/lib/std/tmux/tmux_api_spec.spl`; the `--json` envelope reads
`total_failed:0` but also `total_passed:0` / `success:false` both before and
after the fix — a pre-existing aggregation quirk of the seed `--json` path, not
caused by this change and not touched here.
