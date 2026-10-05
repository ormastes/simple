# JIT: declared typed-bytes externs spliced to the interpreter (wrong values, O(n) per call)

- **Found:** 2026-10-05 while timing `std.common.image.png_encode` under `simple run`.
- **Status:** fixed in the change that adds this record.

## Symptom

A module that declares one of the typed-bytes accessors itself, e.g.

```simple
extern fn rt_typed_bytes_u8_unchecked(arr: [u8], idx: u64) -> u64
```

(as `std.common.hash.adler32` and `std.common.crypto.crc32` do), ran those
calls 4-5 orders of magnitude slower under the JIT than under the
interpreter and returned the wrong value:

| loop `s += rt_typed_bytes_u8_unchecked(d, i)` over `[7u8; n]` | n = 16384 | n = 65536 |
|---|---|---|
| interpreter | 22 ms, sum 114688 | 145 ms, sum 458752 |
| JIT (before) | 16 913 ms, **sum 0** | 247 227 ms, **sum 0** |

Every adler32 / crc32 user under the JIT (PNG encode/decode, zlib, DBFS
checkpoints) paid this: encoding a 128x128 PNG took 90 s (adler 51 s,
crc 27 s) versus 2.1 s interpreted.

## Root cause

`run_file_jit` (`src/compiler_rust/driver/src/exec_core.rs`) treats every
declared extern whose name the JIT symbol provider cannot resolve as
"unresolvable" and rewrites its calls through `apply_hybrid_transform` into
interpreter-bridge calls. The JIT runtime exports no symbol for most
typed-bytes accessors because Cranelift codegen always lowers them inline
(`compile_call` in `codegen/instr/calls.rs`: `compile_inline_bytes_u8_at`,
`compile_inline_typed_bytes_le_unchecked`, `compile_inline_typed_bytes_data_at`,
`compile_inline_typed_words_*`). The hybrid rewrite runs before codegen, so
the inline lowering never saw the calls; each one crossed the bridge, which
converts the packed `[u8]` into a boxed interpreter array (O(n) per call) and
whose result came back as 0.

## Fix

- `codegen::instr::calls::is_inline_lowered_byte_accessor(name)` lists the
  accessors codegen always lowers inline; `run_file_jit` no longer counts them
  as unresolvable externs, so their calls reach the inline lowering.
- The pre-finalize NULL-jump guard (`first_unresolved_import_called` in
  `codegen/jit.rs`) skips these names: their `Linkage::Import` declaration
  (created by the source `extern fn`) is never called, because every call
  site is lowered inline. Without this, the first fix step merely moved the
  failure: the whole module dropped to the interpreter with
  "unresolved external symbol 'rt_typed_bytes_u8_unchecked' would NULL-jump".
- The interpreter had no handler for `rt_typed_bytes_u8_at` and
  `rt_typed_bytes_u32_le_unchecked` ("unknown extern function"); both now map
  to the existing byte readers, so the two lanes accept the same declarations.
- Once the calls reached the inline lowering, a second defect showed: the
  hosted (non-FAM) branch of `compile_inline_typed_bytes_le_unchecked` and
  `compile_inline_bytes_le_at` read packed bytes unconditionally, but a `[u8]`
  built in a function with a runtime length (`[0u8; n]`) is a SLOT array
  (8-byte tagged elements), so the read returned slot-word bytes (a 16-byte
  sum of 2040 read 105). `hosted_bytes_le_load` now branches on the packed
  flag (gc_flags bit 3, as `compile_inline_bytes_u8_at` already did) and
  composes slot arrays from per-slot byte decodes.
- The five inline lowerings treat an unused result (`dest == None`) as a
  no-op instead of declining (they are pure reads; declining would fall back
  to the missing runtime symbol).
- The bridge's packed-`[u8]` conversion itself is NOT changed here (owned by
  the runtime array-layout audit); this fix simply stops routing inline-able
  accessors through it.

## Result

`std.common.image.png_encode` of a 128x128 image under `simple run` (JIT):
90.6 s -> 10 ms (adler32 51 s -> <1 ms, crc32 27 s -> <1 ms); output is
byte-identical (the encoder itself was never quadratic — its `_extend`
copies were measured linear, 1 ms for 2 x 64 KiB).

## Specs

- `test/01_unit/compiler/typed_bytes_extern_jit_parity_spec.spl` (3/3; 0/3
  on the pre-fix binary) runs
  `test/fixtures/jit_typed_bytes/typed_bytes_extern_probe.spl` (256 KiB) under
  the JIT and the interpreter: same values, equal to zlib's adler32/crc32;
  JIT finishes inside a 120 s timeout (pre-fix: hours); the engine receipt no
  longer names any `rt_typed_bytes` symbol as spliced.
