# File text codec sessions cost ~32 us/byte under the interpreter, ~3.3 GB RSS under JIT

- Status: open (perf regression; owner = text-codec chain 153c3df094e / d0f24c53365 / 8a17d0ee7c3)
- Found: 2026-10-19 while fixing `seed_interpreter_text_codec_file_io_empty` (interpreter byte-array contract)

## Measurement

Bench: write a 1 MiB text with `std.io_runtime.file_write` 5x, then `file_read` it 5x.
Seed built from this lane (sha256 f49a027986fb...), `MemoryMax=6G` scope.

| stdlib | mode | write x5 | read x5 | max RSS |
|---|---|---|---|---|
| pre-codec `31e45c70df3` | interpreter | 2 ms | 1 ms | 82 MB |
| pre-codec `31e45c70df3` | jit | 2 ms | 1 ms | 167 MB |
| codec (`387af110552` + fix) | interpreter | 166 s | 169 s | 243 MB |
| codec (`387af110552`) | jit | 1.7-2.3 s | 2.7-3.2 s | 3.36 GB |

Scaling is linear (64 KiB: 2.0 s, 256 KiB: 8.3 s, 1 MiB: 33 s per op): it is
per-byte interpretation, not quadratic copying.

## Cause

`src/lib/nogc_sync_mut/io/file_text_session.spl` and the external-text codec
(`src/lib/common/encoding/external_text.spl`, `io/external_text_io.spl`) move and
validate every byte in Simple loops (`for byte in chunk: bytes.push(byte)`,
grow-by-copy, per-byte UTF-8 validation), where the pre-codec path made one
runtime call (`rt_file_write_text` / `rt_file_read_text`).

## Fix direction

For the UTF-8 / `BomPolicy.Preserve` default codec, validate and convert through
bulk runtime owners (`rt_text_validate_utf8`, `rt_text_to_bytes`,
`rt_bytes_to_text`, bulk byte concat) and keep the per-byte path only for
UTF-16 and BOM handling. Strictness must be unchanged.
