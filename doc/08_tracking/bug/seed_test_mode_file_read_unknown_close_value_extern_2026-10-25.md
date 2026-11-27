# Windows seed `test` mode: `file_read` fails with `unknown extern function: rt_io_file_close_value`

**Status:** open. **Found by:** P-G6 (per-file generic instance jobs), 2026-10-25.

## Symptom

On Windows, with `C:/dev/simple/bin/simple.exe` (40,552,960 bytes, 2026-10-25 12:58),
every `std.io_runtime.file_read` call inside a spec run by `simple.exe test`
fails with:

    semantic: unknown extern function: rt_io_file_close_value

`file_read` -> `file_read_result` -> `FileTextSession.close` ->
`io_file_close` (`src/lib/nogc_sync_mut/sffi/fs.spl:276`) calls the i64 twin
`rt_io_file_close_value`. The interpreter extern table registers only
`rt_io_file_close` (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1639`);
the twin exists only in codegen (`codegen/runtime_sffi.rs:2344`) and the
runtime crate. `--mode smf` degrades to the interpreter and fails the same way.

The same `file_read` works under `simple.exe run` (hybrid JIT splice).

## Impact

Any spec that reads a file it wrote fails in `test` mode on this host, e.g.
`test/01_unit/compiler/cache/package_archive_cache_spec.spl` (6 of 9 fail) and
`test/01_unit/compiler/driver/native_file_worker_instances_v1_spec.spl`
(4 of 7: every case that re-reads the instance cache header or the
previous-needed set).

## Fix direction

Register `rt_io_file_close_value` (fd -> 0/1) in the seed interpreter extern
table next to `rt_io_file_close`, then redeploy the Windows seed.
