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

Step 1 (c7156d92707) routed hoisted `[u8]` reads through the header-checking
`rt_typed_bytes_u8_unchecked`: correct, but ~20% slower on the hoisted loop.
Step 2 replaces it with a loop-invariant layout check:

- `mir/lower/lowering_stmt.rs` (hoisted-loop preheader): besides `rt_array_data_ptr`,
  call `rt_array_is_byte_packed(array)` once and build a layout-tagged pointer
  `data_ptr | (1 - (packed & 1))` (bit 0 set = slot layout; data pointers are
  8-aligned). The `& 1` masks the C twin's `int` return.
- `mir/lower/lowering_expr_struct.rs` (u8 index arm): hoisted reads use
  `rt_typed_bytes_u8_data_at(tagged_ptr, i)`.
- Cranelift (`codegen/instr/calls.rs`): `rt_array_is_byte_packed` is inlined (flag
  load; 0 on FAM/freestanding); `rt_typed_bytes_u8_data_at` branches on bit 0 of
  the pointer register (packed byte load vs slot decode). No per-read header load.
- `rt_typed_bytes_u8_data_at` runtime twins (Rust `collections.rs`, C
  `runtime_native.c`) honour the same bit-0 tag; an untagged aligned pointer reads
  packed bytes exactly as before. `rt_array_is_byte_packed` already existed in C;
  this adds the Rust twin (`collections.rs`) and registers it (`runtime_sffi.rs`,
  `elf_utils.rs`, runtime `lib.rs`/`value/mod.rs`).

Perf (JIT, typed packed `[u8]` sum, 10.5M reads per loop, 7 runs, seed 82f595a9 base
/ e09aa1f2 fix): hoisted `val n = data.len(); while i < n` 14-15 -> 13-15 ms;
non-hoisted `while i < data.len()` 21-22 -> 21-22 ms; RSS 158-173 MB both. zstd JIT
16/64 KiB levels 1/3/19 decode: within noise.

Byte order: the Cranelift packed 4/8-byte loads in `hosted_bytes_le_load` carry an
explicit little-endian `MemFlags`; the LLVM typed-bytes 4/8-byte arms
(`compile_inline_typed_bytes_le_unchecked`, the checked `typed_bytes_le` arm) now
compose bytes with shifts (`build_le_bytes_compose`). Slot arms compose from the
decoded value. The C (`rt_bytes_u64_le_at`), Rust runtime (`from_le_bytes`) and
interpreter (shift loop) readers were already explicit LE.

Tests: `src/compiler_rust/compiler/tests/jit_hoisted_u8_read_slot_layout.rs`
(u64 index sum 815 -> 1515, mid-array tail 4294967295 -> 3012, hoisted MIR shape:
one layout check + one tagged read + no unchecked read, LE pinned values
0x04030201 / 0x0807060504030201 on packed and slot arrays for Cranelift and an LLVM native build in `tests/llvm_typed_bytes_le_native.rs`);
runtime `hoisted_u8_read_follows_the_layout_tag`; C
`rt_bootstrap_c_lane_bucket2_misc_selfcheck.c` tagged-slot cases.

## Still open

- Pure-Simple twin: `src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl:712-714`
  maps the same names; it needs the same review before the self-hosted JIT is default
  (an untagged pointer keeps the old packed-only behaviour there).
- (Fixed) The LLVM typed-bytes arms (`rt_typed_bytes_u{8,32,64}` unchecked and the
  checked `typed_bytes_le` arm) read packed bytes without the flag check: the native
  LLVM LE test returned `le=30` (slot-layout reads 0). `build_le_bytes_compose` now
  branches on the packed flag and composes bytes with shifts in both arms: `le=33`.
  Verified with `LLVM_SYS_231_PREFIX=/home/yoon/dev/llvm/install-23.1.2`. The
  in-process LLVM JIT (`LocalExecutionManager` Llvm) segfaults on any `[u8]` push,
  independent of this bug, so the LLVM test builds a native executable.

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
