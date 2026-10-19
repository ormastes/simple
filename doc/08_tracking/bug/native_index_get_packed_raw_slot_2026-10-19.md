# Native `rt_index_get` returned the raw slot of packed `[u8]`/`[u64]` arrays

**Status:** RESOLVED 2026-10-19 (branch `work/native-u8-untyped-boxing`, two commits).
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

Every C accessor that hands a packed element to Simple code now goes
through `spl_core_array_value_at`. That helper returns `rt_value_int(byte)` for
BYTES and `rt_value_int(word)` for U64_PACKED, the exact twin of Rust's
`RuntimeValue::from_int`. A word of 2^60 or more becomes a lossless signed
wide box, which `UnboxInt` (`rt_value_unbox_int`) and `rt_value_as_u64` both
decode. `rt_array_get` keeps its raw-slot contract, which C internals use and
`rt_array_packed_reverse_index_enumerate_selfcheck.c` pins.

The second commit covers:
- now tagged: `rt_index_get`, `first`, `last`, `at`, `pop`,
  `map`/`each`/`reduce`/`filter`/`find`/`all`/`any`(`_truthy`),
  `enumerate`, `take`/`drop`, `max`;
- now matched numerically like `index_of`'s packed arm: `contains`;
- now raw in-place swap or qsort instead of a `rt_array_set` round trip that
  re-decoded 56 as 7: `reverse` (in place) and `sort` (in place);
- now unsigned: packed `[u64]` to_text;
- now also matches wide or negative needles on `[u64]`: `index_of`.

These were already correct: `sum`, `remove`, `slice`, `sorted`/`rev` (copy
keeps the layout), `rt_array_take`, `for` iteration, and `concat`/`copy`.

`test/01_unit/runtime/runtime_native_focus_test.c:144` asserted the old raw
`rt_array_last` result for a byte array (`== 255`). It now asserts
`rt_value_int(255)`, because that line was pinning the bug.
`rt_core_exports_behaviour_selfcheck.c` failed at base and passes now.

Typed hot paths are unchanged. No compiler source changed, so MIR is
identical, and typed `[u8]`/`[u64]` reads inline `rt_typed_bytes_u8_*` /
`rt_typed_words_u64_*`. A typed `[u8]`/`[u64]` loop program's unstripped
binary differs from base in exactly one instruction: an `add` immediate that
addresses `.rodata` (string layout). `spl_main` disassembles identically.

## u64 >= 2^60 semantics

Interpreter, JIT and native now agree on the values (`first`, `last`, `[0]`,
`pop` of `[2^60+5, 8, u64::MAX]`). Native and the interpreter print the
array as `18446744073709551615`. The JIT prints `-1`; that is Rust-runtime
array formatting and is not fixed here.

## Tests

- `src/runtime/test/rt_index_get_packed_tagged_selfcheck.c` (105 checks:
  0, 7, 8, 56, 64, 255, and u64 2^60+5 and u64::MAX)
- `src/compiler_rust/driver/tests/native_untyped_packed_index_parity.rs`
  (3 tests, native == interpreter)

## Still open (not packed-slot defects)

- `any`/`all` return a raw bool, and an untyped `index_of(8)` misses. This
  happens on generic `[i64]` too, in both native and JIT.
- The interpreter gets `[u8].max()`/`sorted()` wrong (64 and 255 for
  `[56,7,8,0,255,64]`) and wraps a `for` sum over `[u8]` at 256. The JIT
  gives 231/117. Native gives 255/64/390, which are correct.
- The JIT corrupts a `[u8]` after untyped `reverse()`/`pop()` on a
  `.copy()`; the probe printed `[8, 47, 7, 202, ...]`.
- Floats are wrong in all three modes when read from an untyped array
  element into a typed `f32`/`f64` binding (interpreter: `f32=0.0`).
- An accumulator `sum = sum * 31 % 1000000007 + v` over 42 bytes printed
  `199` in the interpreter and a large value natively. Not investigated.
- Standalone native still refuses `?` (`gzip_decompress`, zstd decoders).
  That is being fixed on `work/smf-standalone-bundles`.
