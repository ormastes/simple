# Native SQLite C result ABI mismatch

## Status

Source-fixed; focused native execution is pending an unloaded incremental lane.

## Reproduction

The public `sqlite_sffi.spl` wrappers and interpreter define success/row-ready
as tagged integer `1` and failure/end-of-rows as tagged integer `0`. The C
provider instead returned `0` on success, `-1` on failure, and special booleans
from `rt_sqlite_query_next`, so native callers comparing the result with `1`
observed successful operations as failures.

## Fix and prevention

`runtime_sqlite.c` now returns tagged integer `1` or `0` for close, execute,
bind, reset, transaction, and query-next operations, matching the public Simple
and interpreter contract. The existing C-provider round-trip probe now checks
create, insert, row-ready, end-of-rows, invalid SQL, and close results. A
pure-Simple Stage4 provider spec also pins the public wrapper and C encodings.

No bootstrap, native executable, or package execution is claimed while other
native/bootstrap jobs own the machine.
