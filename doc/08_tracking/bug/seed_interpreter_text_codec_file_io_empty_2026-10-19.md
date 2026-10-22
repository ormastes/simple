# Seed interpreter: every codec-session file read/write fails (file_write false, reads empty)

- Status: open (product bug, needs an owner lane)
- Found: 2026-10-19 while making `simple test` run on `59d84defe67` with the seed from that tree

## Symptom (seed interpreter, `SIMPLE_EXECUTION_MODE=interpreter`)

- `std.io_runtime.file_write` and `std.nogc_sync_mut.io.file_ops.file_write` return
  `false` for any path (`/tmp/x`, `build/x`, or a fresh `secure_temp_dir`).
- `file_read_text("VERSION").len()` returns `0`. VERSION is 11 bytes.
- So `process_run_timeout` returns empty stdout/stderr even for `/bin/echo hi`,
  because it captures through temp files and reads them back with `file_read_text`.
- `file_default_text_codec()` returns
  `Err: external text at byte -1: external text byte buffer allocation failed`.

## Root cause

`text_byte_buffer` (`src/lib/common/text_bytes.spl:20-24`) treats
`rt_array_data_ptr(rt_byte_array_new(capacity)) == 0` as an allocation failure. The
seed interpreter breaks that contract in two ways:

1. `rt_array_data_ptr` (`src/compiler_rust/compiler/src/interpreter_extern/memory.rs:1862`)
   returns 0 for any empty byte array. The interpreter says that is legitimate
   ("callers MUST fall back"), so `text_byte_buffer(0)` gives `Err`.
2. `rt_byte_array_new(n)` (`interpreter_extern/sffi_array.rs:60`) returns n zero
   bytes, so `len == n`. The stdlib contract says "logical length remains zero":
   `text_byte_buffer(8).len()` is 8 in the interpreter. If only (1) is fixed,
   writes would succeed and carry NUL-prefixed garbage.

Introduced by today's text-codec chain: `153c3df094e` (external text foundation),
`d0f24c53365` (text session codec), `8a17d0ee7c3` (route file text through bounded
codec sessions). Base `59d84defe67` carries all three.

## Blast radius

Any spec, or any runner path, that writes a file or reads one as text through these
providers, or that captures process output with `process_run_timeout`. It also
silently breaks test-DB/doc writes and structured-evidence files in sweeps.
Example: `test/01_unit/test_runner/test_runner_vacuous_expectations_spec.spl`, where
2 of 8 examples fail on a fixture `file_write`.

## Unblock condition

The owner decides which side changes: the interpreter externs (give
`rt_byte_array_new` capacity semantics with len 0 and a non-zero pointer for
capacity 0), or `text_byte_buffer` (stop using a raw pointer as the allocation
oracle). Then re-run the specs above.
