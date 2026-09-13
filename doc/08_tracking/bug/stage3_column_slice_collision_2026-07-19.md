# Stale Stage3 stole text `slice` calls for `Column.slice`

- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Observed:** a strict focused lint link resolved text `slice` calls in several modules as `Column_dot_slice` and failed because the table owner was outside the entry closure.
- **Cause:** the deployed Stage3 predates current receiver-owner resolution and globally selected the same-named `Column.slice` method. Its shared cache also retained dependent objects after the method owner changed.
- **Fix:** rename the table-only operation to `Column.slice_rows` and update its two `Table.head`/`Table.tail` callers. No other in-repo caller used that API. This is a deployed-Stage3 compatibility workaround; external callers of the old exported table surface must migrate until a current owner-resolution compiler is deployed.
- **Regression:** a fresh isolated strict lint shard compiled 655 modules, linked successfully with zero failures, and contained no `Column_dot_slice` error. Reusing the old cache reproduced the stale-object failure, so verification must use an isolated shard after method-owner changes until dependency invalidation is fixed.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
