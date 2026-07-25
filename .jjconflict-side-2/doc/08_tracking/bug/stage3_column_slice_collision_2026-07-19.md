# Stale Stage3 stole text `slice` calls for `Column.slice`

- **Status:** compatibility fix passed strict incremental link
- **Observed:** a strict focused lint link resolved text `slice` calls in several modules as `Column_dot_slice` and failed because the table owner was outside the entry closure.
- **Cause:** the deployed Stage3 predates current receiver-owner resolution and globally selected the same-named `Column.slice` method. Its shared cache also retained dependent objects after the method owner changed.
- **Fix:** rename the table-only operation to `Column.slice_rows` and update its two `Table.head`/`Table.tail` callers. No other in-repo caller used that API. This is a deployed-Stage3 compatibility workaround; external callers of the old exported table surface must migrate until a current owner-resolution compiler is deployed.
- **Regression:** a fresh isolated strict lint shard compiled 655 modules, linked successfully with zero failures, and contained no `Column_dot_slice` error. Reusing the old cache reproduced the stale-object failure, so verification must use an isolated shard after method-owner changes until dependency invalidation is fixed.
