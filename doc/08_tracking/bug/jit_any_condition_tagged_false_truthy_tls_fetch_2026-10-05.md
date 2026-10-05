# JIT: a condition on an `ANY` value tested the tagged word, so `false`/`nil` were truthy

**Date:** 2026-10-05
**Status:** Fixed (seed MIR lowering)
**Symptom:** under the JIT every https fetch in the browser failed with
`h1: TLS read failed or timed out for example.com:443`; interpreted, it worked.

## Root cause

`h1_client.spl` reads the response through `read_tls_response_bytes`, which
returns `Pair<[u8], bool>`, then computes:

```
val unclean_eof = read.second or closed.is_err()
```

`Pair<K, V>.second` is a type-parameter field, lowered as `ANY`: a tagged
`RuntimeValue`. MIR `Branch`, the `and`/`or` short-circuit and `not` test the
raw machine word, and a tagged `false` (and `nil`) is a non-zero word. So
`false or false` was `true`, and a complete 930-byte example.com response was
refused as an unclean EOF. Instrumented under JIT:

```
second=false closed_err=false len=930 selfdelim=false unclean=true
```

The low-level TLS externs were never the problem: a direct
connect/write/read/close probe returned the same 930 bytes on both lanes.

Minimal repro (JIT prints `TAKEN`, interpreter does not):

```
val a = Pair(1, false)
if a.second:
    print "TAKEN"
```

## Fix

`MirLowerer::lower_condition_expr` (`mir/lower/lowering_core.rs`) lowers a
condition and, when its type is `ANY`, decodes it through `rt_value_truthy` —
the interpreter's truthiness (`false`, `nil`, `0`, `0.0` falsy; heap objects
truthy). Used by `if`/`elif`, `while`, `assert`, `assume`, the if-expression,
both sides of `and`/`or` (also the coverage variant), and `not`. Typed `bool`
conditions are unchanged (no extra call).

## Evidence

- Cargo: `mir::lower::tests::branch_coverage::types::any_condition_decodes_truthiness`
  (each condition form emits `rt_value_truthy`; a typed bool does not).
- Specs (semantics on both lanes): `test/01_unit/compiler/generic_bool_field_condition_spec.spl`
  (the exact Pair shape) and `test/01_unit/compiler/any_value_condition_spec.spl`
  (generalization: `any` params, untyped `list` elements, nil/0/text). Note:
  `it` bodies currently execute on the interpreter even under `run`, so these
  pin the semantics; the JIT lowering is pinned by the cargo test and the
  probe below.
- JIT probe, before/after: `count_false=111` -> `1000` for
  `if p.second` / `or` / `and` / `not` on `Pair(1, false)`.

## Second root cause on the same path: `rt_slice` ignored packed arrays

With the condition fixed, the JIT fetch got further and failed with
`h1: invalid HTTP version in status line: '?D ...'`. The 931 response bytes
were intact up to `parse_http_response_bytes`; `raw.slice(0, i)` in
`split_header_body_bytes` returned garbage. A fetched `[u8]` is a BYTE-PACKED
`RuntimeArray`, and `rt_slice` (`runtime/src/value/collections.rs`) copied
`(*arr).as_slice()`, which reads the buffer as `len` 8-byte tagged slots:
every element was 8 ASCII bytes glued into a word (`0x4f203430202c6e75` =
"un, 04 O"), and the read ran 8x past the end of the byte buffer
(out-of-bounds read). Small literal arrays are not packed, which is why
isolated probes passed.

Fix: `rt_slice` keeps the source layout for byte-packed and u64-packed arrays
(same approach `rt_array_concat` already took). Cargo:
`value::collection_tests::test_slice_packed_arrays_keep_elements`.

**Open class (not fixed here):** `as_slice()` has ~113 call sites in the
runtime; any that do not check `is_byte_packed()`/`is_u64_packed()` first have
the same defect for packed arrays. Owner: whoever owns the packed-array
(`Value::Array`) layout work. Repro shape: build a `[u8]` from a runtime text
(`text_to_bytes` of a fetched chunk) and call the method under the JIT.

## Also observed, not fixed

- `"x" * 4000` evaluates to length `-1` under the JIT (4000 interpreted).
- (Retracted) the garbage `parts.first[0] as i64` values came from the broken
  `rt_slice`, not from `Cast` ANY -> I64, which already decodes via
  `rt_value_as_int`.

## Related lane-parity defect: `rt_sha256_write` / `rt_sha1_write` took a raw pointer

Reported by the CSS agent: under the JIT the `rt_sha256_*` stream returned a
wrong digest (`"abc"` -> `736722f2...`; here `faee9357...`, the value depends
on the address) while the interpreter returned `ba7816bf...`. The interpreter
wrapper (`interpreter_extern/sha256.rs`) accepts `rt_sha256_write(h, data:
text | [u8], len)`, but the native symbol was `(handle, *const u8, u64)`.
Compiled code passes `data` as a tagged `RuntimeValue`, so the runtime hashed
the memory the tagged word happened to point at, an out-of-bounds read.
`rt_sha1_write` had the identical signature.

Fix: both native writes take `(handle, data: RuntimeValue, len: i64)` and read
the bytes from a text or a `[u8]` (byte-packed or slot) value, which is the
interpreter's contract. A payload that is neither, or a `len` that is negative
or longer than the payload, drops the handle, so `finish` returns NIL (fail
closed) instead of a digest of the wrong bytes. No C-runtime twin exists for
either symbol. Cargo:
`value::sffi::hash::sha256::tests::test_sha256_write_takes_runtime_payload`
(text, byte-packed `[u8]`, slot `[u8]`, three fail-closed shapes); the sha1
tests were moved to the value ABI, and the null-pointer test became
`test_sha1_nil_data_fails_closed`.

## Related: pure-Simple inflate returned nil under the JIT (PNG path)

`deflate_inflate_zlib_bounded` on the 13-byte zlib stream for "hello"
(`78 9C CB 48 CD C9 C9 07 00 06 2C 02 15`) failed under the JIT ("DEFLATE
stream is invalid") and decoded correctly in the interpreter. The decoder
(`nogc_sync_mut/compression/gzip/{inflate,huffman}.spl`) keeps its reader
state in an untyped `[Any]`, so `data[byte_pos].to_i64()` has an ERASED
receiver. A bare `to_i64` on an erased receiver with no user method falls to
the codegen builtin, which routed it to `rt_to_int_dynamic`. That helper
returns any non-text value VERBATIM, and for a tagged int that is `n << 3`:
byte `0xCB` (203) read as 1624, so every bit the reader extracted was wrong.

Fix: new `rt_any_to_int` (Rust runtime `value/collections.rs` + C twin
`src/runtime/runtime_native.c`, declared in `runtime.h`, registered in
`runtime_symbols.rs` / `runtime_sffi.rs` / codegen roots): text parses, float
truncates, everything else decodes tag-aware (`rt_value_unbox_int`). Codegen
(`try_compile_builtin_method_call`) uses it for a BARE int-cast name (only
emitted for erased receivers) whose codegen type is ANY or unrecorded. An
explicitly raw `I64` receiver keeps the old path, because decoding a raw word
would shift it. Cargo: `value::collection_tests::test_any_to_int_decodes_tagged_values`.

Two more defects on the same inflate path, found after `to_i64` was fixed
(the decoder then produced `8 5 12 12 15` for `hello`, i.e. `(v << 3) & 0xFF >> 3`):

- The narrower integer casts on an erased receiver (`symbol.to_u8()`) were
  typed `ANY` in HIR while `to_i64` was typed `I64`, so consumers disagreed:
  a `[u8]` push took the result raw and `as i64` decoded it as tagged
  (`104.to_u8()` -> pushed 64, read back 8). HIR now types every integer cast
  on an ANY receiver as its raw target type (`hir/lower/expr/mod.rs`), and
  codegen produces `rt_any_to_int` + narrow for all of them.
- `out.push(x)` into a typed `[u8]` with an `ANY` argument
  (`out.push(block_out[k])`, `block_out` from an `[Any]` slot) passed the
  tagged word to `rt_typed_bytes_u8_push`, which stores its low byte. MIR now
  decodes an `ANY` argument first (`lowering_expr_method.rs`). Cargo:
  `mir::lower::tests::branch_coverage::types::any_push_into_u8_array_is_decoded`.

Open (not fixed here): the same "tagged ANY into a typed raw slot" shape
likely exists for `[u8]` index-set and the other typed push helpers (u32,
u64); not reproduced yet.

After these fixes `deflate_inflate_zlib_bounded` on the "hello" stream returns
Ok under the JIT. The Adler-32 trailer check runs over the decoded bytes, so
the output is byte-exact.

**Resolved below (follow-up section):** `for b in (f() ?? [])` over a
`[u8]` reads the FIRST element double-decoded under the JIT (`104 101` ->
`13 101`; index reads and the `f()!` path are correct). Reproduces on a seed
built before any of this work. Repro: `build/probe/forin_probe.spl` shape:
`fn mk() -> [u8]?` returning `[104u8, 101u8]`, `val a = mk() ?? []`, then
`for b in a: print b`.

## Follow-up 2026-10-05: the for-in first-element misread was a byte-packed read, plus `text * int`

**for-in over a byte-packed `[u8]`** (was recorded above as "first element of
`f() ?? []`"). The `??` was incidental. The codegen inline fast path for
`rt_array_get` (`codegen/instr/calls.rs::compile_inline_array_get`) returned
the RAW byte for a byte-packed array, while the runtime `rt_array_get`
returns a tagged int (`from_int`) and every MIR consumer decodes the result
(UnboxInt). The decode is tag-aware, so a byte whose low 3 bits are zero was
shifted (104 -> 13, 8 -> 1, 0 stays 0) and every other byte passed through.
That is why only "the first element" of `hello` looked wrong. This most
likely surfaced when #2495 moved for-in over arrays from `rt_index_get` (no
inline path) to `rt_array_get`, so every `for b in bytes` under the JIT could
corrupt multiples of 8 since then. Fix: the inline byte path tags its result
(`byte << 3`), matching the runtime function.

**`text * int`** fell through MIR to a native `imul` on the string pointer,
so `"x" * 4000` was not a string (len -1, and it blanked any interpolation it
appeared in). MIR now lowers `text * int` and `int * text` to the existing
`rt_string_repeat` (both runtime lanes), which matches the interpreter
(count <= 0 -> "").

Evidence: JIT-executed `compiler/tests/jit_value_lane_parity.rs`
(`for_in_over_packed_bytes_reads_every_byte`, `text_times_int_repeats`), and
MIR test `text_times_int_lowers_to_string_repeat`.
