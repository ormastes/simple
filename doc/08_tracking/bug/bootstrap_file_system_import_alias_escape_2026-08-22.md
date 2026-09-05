# Bootstrap file-system import alias escape

## Category

The admitted Pure-Simple Stage-2 compiler lost qualified imported-module
aliases while compiling selected bodies in `nogc_sync_mut/file_system`.
`dir_ops`, `metadata`, `utilities`, and `watch` consequently failed strict
native compilation with unresolved `types`, `file_ops`, `dir_ops`, `path_ops`,
or `metadata` `GlobalLoad` values.

The repair binds imported types and functions directly with explicit local
aliases, and confines the affected calls to private function-level `@unsafe`
compatibility leaves. Public APIs and their validation/result behavior remain
safe and unchanged. Leaves forward their existing arguments and results; the
change adds no collection, buffer, copy, scan, retry, or allocation.

## Bounded evidence

One combined entry closure bound all four owners under
`SIMPLE_NO_STUB_FALLBACK=1`, using a dedicated cache and the admitted
Pure-Simple Stage-2 compiler. The initial attempt confirmed that function-level
metadata alone did not retain qualified aliases: 10 bodies failed in 1.42 s at
163,840 KiB maximum RSS.

The one permitted retry, after direct-symbol import binding, completed with
zero body failures and zero stub fallbacks in 14.20 s at 163,228 KiB maximum
RSS. Logs, `/usr/bin/time -v` receipts, entry source, and isolated cache are in
`build/native_probe/mcdc_cycle4_filesystem_unsafe/`.

This is focused bootstrap-compatibility evidence, not a full compiler build or
a Stage-4 acceptance result.
