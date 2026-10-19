# Seed JIT: hoisted `[u8]` data pointer reads slot-layout arrays as packed bytes (2026-10-19)

Status: FIXED in the seed (Cranelift JIT path), branch `work/jit-u8-hoisted-read-layout`.
No library workaround: `xxhash.spl` reads `data[pos]` normally (a direct `rt_*` read
there would break the no-direct-rt ratchet). Pure-Simple compiler twin still open (below).

## Symptom

Under the seed JIT (not the interpreter), `zstd_decompress_frame` returned
`ChecksumMismatch("zstd content checksum")` for every checksummed frame whose
content length is not a multiple of 4 (probe frames e1, w31, dup31, dup4095,
w4095, w131073 at level 3). The decoded bytes were correct; only the XXH64 over
them was wrong. The encoder was hit the same way: `zstd_compress_frame` on a
slot-layout input wrote a checksum that host `zstd -d` 1.5.5 rejects.

## Minimal repro

```
struct Holder:
    bytes: [u8]

fn tail_sum(data: [u8]) -> u64:
    val total_len: u64 = data.len().to_u64()
    var pos: u64 = 0
    var s: u64 = 0
    while pos < total_len:
        s = s + data[pos].to_u64()
        pos = pos + 1
    s

fn main():
    var slot = Holder(bytes: []).bytes
    var i = 0
    while i < 5:
        slot.push((i + 1).to_u8())
        i = i + 1
    print("sum=" + tail_sum(slot).to_text())

main()
```

Seed sha256 `52280a8bf1abe020b6d3b0f0b1605b2858a6b1cba00a90d953f33c9c1ca01dab`
(built from `origin/release_phase3` 267283d5057):
`SIMPLE_EXECUTION_MODE=interpreter` -> `sum=15`; JIT -> `sum=8` (`1 << 3`, the low
byte of the first tagged slot; the other four slots' byte offsets 1..4 read 0).

## Root cause

A `[]` literal in a struct-field position builds a slot-layout array (8-byte
tagged elements). A typed `var x: [u8] = []` builds the byte-packed layout
(`gc_flags::BYTE_PACKED`). Both are legal `[u8]` layouts.

For a `while i < len` loop the MIR lowering hoists the array data pointer
(`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:1476`) and lowers
`data[i]` on a `[u8]` to `rt_typed_bytes_u8_data_at(data_ptr, i)`
(`mir/lower/lowering_expr_struct.rs:458`). That path has lost the array header,
so it cannot check the layout flag:

- Cranelift: `codegen/instr/calls.rs:1789` `compile_inline_typed_bytes_data_at`,
  hosted arm loads `*(data_ptr + index)` as a byte.
- Runtime: `src/compiler_rust/runtime/src/value/collections.rs:1219`
  `rt_typed_bytes_u8_data_at`, same raw byte load.
- LLVM backend: the typed-bytes arms in `codegen/llvm/functions/calls.rs`
  (around line 1994) need the same review.
- Pure-Simple twin: `src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl:712-714`
  maps the same `rt_typed_bytes_u8_unchecked` / `rt_typed_bytes_u8_data_at` names.

The non-hoisted readers (`compile_inline_bytes_u8_at`, `hosted_bytes_le_load`,
`calls.rs:643-697`) branch on the packed flag and are correct. That is why the
32-byte stripe and 8/4-byte word reads in XXH64 were right and only the 1-3 byte
tail was wrong.

## Fix

`mir/lower/lowering_expr_struct.rs` (u8 index arm): a `[u8]` read never goes
through the hoisted data pointer. Inside a len-bounded loop it lowers to
`rt_typed_bytes_u8_unchecked(array, i)`: still no bounds check, but the inline
read branches on the packed flag (`hosted_bytes_le_load`). The `[u32]`/`[u64]`
hoisted reads are unchanged (they already decode tagged slots).
`rt_typed_bytes_u8_data_at` (codegen `calls.rs` and runtime `collections.rs:1219`)
is no longer emitted by the seed's MIR for `[u8]`; neither file's byte-read logic
changed. It is not dead: the self-hosted twin (`collection_opt_core.spl:714`) still
emits it.

Perf (JIT, typed packed `[u8]` sum, 10.5M reads per loop, 5 runs, seeds
82f595a9 base / 4a91eea4 fix): `val n = data.len(); while i < n` (hoisted) 14-15 ms
-> 17-18 ms (~20%, ~0.3 ns/read); `while i < data.len()` (not hoisted) 22 -> 22 ms;
RSS ~166-171 MB both. zstd 16/64 KiB levels 1/3/19 decode: within noise. A
per-loop hoisted packed flag would recover the hoisted case but needs a new runtime
symbol (C + Rust twins); not done here.

Byte order: the packed 4/8-byte loads in `hosted_bytes_le_load` now carry an
explicit little-endian `MemFlags` (no-op on LE hosts). The slot arm composes bytes
with shifts from the decoded value. The C (`runtime_native.c rt_bytes_u64_le_at`),
Rust runtime (`from_le_bytes`) and interpreter (shift loop) readers were already
explicit LE.

Test: `src/compiler_rust/compiler/tests/jit_hoisted_u8_read_slot_layout.rs`
(u64 index sum 815 -> 1515, mid-array tail 4294967295 -> 3012; i64 index already green).

## Still open

- Pure-Simple twin: `src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl:712-714`
  maps the same names; it needs the same review before the self-hosted JIT is default.
- LLVM backend packed 4/8-byte LE loads (`codegen/llvm/functions/calls.rs`, typed-bytes
  arms) still use host byte order.

## Library sites

- `xxhash64` tail loop: correct once the seed fix is in the binary; no library change.
- `xxhash32` tail loop and the XXH64 streaming finalize loop (`while left > 0`) gave the
  right values on slot-layout input even before the fix.

## Evidence

- Repro: unfixed seed JIT `sum=8`, fixed seed JIT `sum=15`; interpreter `15` both.
- `kat_run.spl` probe (slot-layout `abc` and 39-byte phrase, unmodified `xxhash.spl`):
  unfixed seed JIT `xxh64_ok=false`, fixed seed `true`; interpreter `true` both times.
- 14 zstd encoder probe frames: all decode under the fixed seed's JIT, from packed and
  slot-layout input arrays, and all decode with host `zstd -dc` to the same bytes.
- `test/01_unit/lib/common/crypto/xxhash_kat_spec.spl` slot-layout cases are
  green before the fix as well, because `bin/simple test` runs specs in the
  interpreter (`jit-bail:no-main-fn`). The spec pins the values; the red/green
  JIT evidence comes from the `run` probe.
