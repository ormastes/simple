# Native `rt_index_get` returned the raw slot of packed `[u8]`/`[u64]` arrays

**Status:** RESOLVED 2026-10-19 (branch `work/native-u8-untyped-boxing`).
**Supersedes the root-cause section of:**
`seed_native_gzip_deflate_miscompile_2026-10-19.md` (commit `35b0151d441` on
`work/smf-standalone-bundles`). With this fix, `gzip_*` / `deflate_*` can be
put back into the compress dynSMF bundle.

## Symptom

`fn f(data): [0, data[0], 0]` with `data: [u8] = [56u8]` gives `56` in the
interpreter and the Cranelift JIT, but `7` in a `compile --native` binary.
`[u64]` behaves the same way. `[i8]`, `[i16]`, `[i32]`, `[u16]`, `[u32]`,
`[i64]` and `[bool]` are correct. `lz77_compress(data, level)` takes an
untyped `data`, so native gzip/deflate output was corrupted (zlib rejected it).

## Root cause

The bug is in the linked core-C runtime, not in MIR or codegen. The MIR for
the repro is correct (checked with `SIMPLE_DUMP_MIR`): an untyped receiver
lowers to `rt_index_get(ANY, BoxInt idx)`, and the ANY result is stored
verbatim. The JIT runs the same MIR against the Rust runtime and is correct.

- Rust `rt_index_get` -> `rt_array_get` (`value/collections.rs:997`) tags
  packed slots with `RuntimeValue::from_int`.
- C `rt_array_get` (`src/runtime/runtime_native.c:8642`) returns the RAW
  slot for BYTES / U64_PACKED arrays. This is the C lane's internal
  convention, and `rt_array_packed_reverse_index_enumerate_selfcheck.c`
  pins it.
- C `rt_index_get` (`runtime_native.c:10558`) passed that raw value straight
  out as a RuntimeValue. A later `UnboxInt` then did `56 >> 3 = 7`.

## Fix

`rt_index_get` now tags the slot with `rt_value_int` when the array is
BYTES or U64_PACKED. `rt_array_get`'s raw contract is unchanged. Typed `[u8]`
and `[u64]` reads never reach this function, because they inline
`rt_typed_bytes_u8_*` / `rt_typed_words_u64_*`. A typed 64 KB zstd + lz4 +
`[u8]` loop program links to a byte-identical binary before and after.

## Tests

- `src/runtime/test/rt_index_get_packed_tagged_selfcheck.c`
- `src/compiler_rust/driver/tests/native_untyped_packed_index_parity.rs`

## Still open

- C method wrappers that forward `rt_array_get` on packed arrays leak raw
  slots in the same way. This is measured: on an untyped `[56u8, 64u8]`
  receiver, native gives `first()=7`, `last()=8`, `map(\x: x)[0]=7`, while
  the interpreter gives 56/64/56. `for b in data` is correct. The functions
  involved are `rt_array_first`/`rt_array_last`/`rt_array_map`
  (`runtime_native.c:17604`/`8680`/`9791`) and the closure helpers next to
  them. They are not fixed here. This is not limited to the untyped
  boundary: typed `val a: [u8] = [56u8, 64u8]; a.first()` / `a.last()` is
  also 7/8 natively and 56/64 in the interpreter.
- Packed `[u64]` words of 2^60 or more are now heap-boxed (lossless) by
  `rt_value_int`. The Rust twin's `from_int` truncates them instead. Small
  values are bit-identical in both.
- Floats are wrong in all three modes (interpreter, JIT and native) when
  they come back from an untyped array element into a typed `f32`/`f64`
  binding (interpreter: `f32=0.0`). That is why the parity test leaves out
  floats.
- An accumulator `sum = sum * 31 % 1000000007 + v` over 42 bytes printed
  `199` in the interpreter and a large value natively. Not investigated.
- Standalone native still refuses `?` (`gzip_decompress`, zstd decoders).
  That is being fixed on `work/smf-standalone-bundles`.
