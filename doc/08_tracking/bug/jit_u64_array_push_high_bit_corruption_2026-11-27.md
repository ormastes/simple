# Seed JIT: `[u64].push(v)` flips bit 62 when `v >= 2^63`

- **ID:** jit_u64_array_push_high_bit_corruption_2026-11-27
- **Severity:** P1
- **Status:** fix-implemented-verification-pending (`waiting-for: Rust seed rebuild`)
- **File:** `src/lib/common/crypto/argon2.spl` (line 284 workaround)

Found 2026-11-27 while flipping the std crypto byte API to `[u8]`
(branch `work/crypto-u8-api-20261127`). Host: aarch64 Linux (DGX GB10).
Seed: `~/.cache/cargo-target-wr-seed1126b/release/simple` (release head 11-26).

## Repro

```
fn main():
    val v: u64 = 13643789653076310793u64
    var a: [u64] = []
    a.push(v)
    var b: [u64] = [0u64; 2]
    b[0] = v
    var c: [u64] = [v, 1u64]
    var d: [i64] = []
    d.push(v as i64)
    print "push={a[0]} idx={b[0]} lit={c[0]} i64push={d[0] as u64} xor={(a[0] ^ v)}"
```

| engine | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `push=13643789653076310793 idx=13643789653076310793 lit=13643789653076310793 i64push=13643789653076310793 xor=0` |
| `SIMPLE_EXECUTION_MODE=jit` | `push=18255475671503698697 idx=13643789653076310793 lit=13643789653076310793 i64push=13643789653076310793 xor=4611686018427387904` |

Only `.push()` into a `[u64]` is wrong; an index store, an array literal and a
push into `[i64]` are exact. The xor is exactly bit 62 (`0x4000000000000000`),
consistent with a tagged-int encode/decode of the pushed word.

## Impact

`std.common.crypto.argon2` builds its 128-word blocks with `[u64].push`, so the
JIT produced a wrong Argon2id tag (RFC 9106 §5.3 vector: got `68372ce3...`,
want `0d640df5...`). Before the `[u8]` API flip this was latent: every program
importing `blake2` demoted the whole module to the interpreter on an unrelated
ambiguous `bytes_to_hex` call, so the JIT never ran argon2.

## Workaround (in tree)

`@workaround(jit_u64_array_push_high_bit_corruption_2026-11-27)` in
`src/lib/common/crypto/argon2.spl`: every `[u64]` word buffer is pre-sized and
index-assigned. Argon2id RFC 9106 vector now passes on interpreter and JIT.

## Fix owed

Seed JIT array push lowering for `u64` element type (Rust seed,
`src/compiler_rust/compiler/src/codegen/`). Remove the workaround once fixed and
the repro above prints `xor=0` on the JIT.

## Root Cause & Fix Implemented (2026-11-27, W8-3)

- **Root Cause:**
  1. Empty array lowering (`hir/lower/expr/collections.rs::lower_array`) ignored `expected_target_type` for `[]` and fell back to `[i32; 0]`, while MIR `Let` initialization (`mir/lower/lowering_stmt.rs`) only had a declared-type packed fast-path for `[u8]` (`is_u8_array_declared`) and not `[u64]`. Consequently `var a: [u64] = []` allocated an **unpacked** `RuntimeArray` (`gc_flags::U64_PACKED == 0`) via `rt_array_new(16)`.
  2. Cranelift `compile_inline_typed_words_push` (`codegen/instr/calls.rs`) called `maybe_packed_u64_store_word`, which on `!u64_packed_condition` stored `value << 3` inline (losing bits 61..63). On read, `compile_inline_typed_words_at` / `maybe_packed_u64_load_word` / `compile_inline_typed_words_data_at` emitted `sshr_imm(raw, 3)` without checking `TAG_INT` or unboxing `HeapUInt`. For `13643789653076310793u64` (`0xbd58_4b84_231b_7c09`), `(v << 3) >>_arith 3 = 0xfd58_4b84_231b_7c09` (bit 62 flipped, `xor = 0x4000_0000_0000_0000`).
  3. In runtime `collections.rs`, non-packed `[u64]` store paths used `RuntimeValue::from_int(value)`, while `rt_typed_words_u64_unchecked` and `rt_typed_words_u64_data_at` omitted `as_heap_u64()` / `as_heap_i64()` decoding.
- **Fix (`src/compiler_rust/**`):**
  1. `src/compiler_rust/compiler/src/hir/lower/expr/collections.rs`: propagate concrete `HirType::Array` element type from `expected_target_type` to empty `[]`.
  2. `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`: allocate `U64_PACKED` buffers (`rt_array_new_with_cap_u64` + `rt_typed_words_u64_push`) for `[u64]` `Let` array literals mirroring `[u8]`.
  3. `src/compiler_rust/compiler/src/codegen/common_backend.rs`: mark `rt_value_u64` as a codegen root alongside `rt_value_as_u64`.
  4. `src/compiler_rust/compiler/src/codegen/instr/calls.rs`: update `maybe_packed_u64_store_word`, `maybe_packed_u64_load_word`, and `compile_inline_typed_words_data_at` (`width == 8 && !ctx.fam_arrays`) to preserve bits 60..63 on unpacked `[u64]` slots via `rt_value_u64` / `rt_value_as_u64` while keeping `U64_PACKED` zero-call inline.
  5. `src/compiler_rust/runtime/src/value/collections.rs`: use `encode_unpacked_u64_slot` (`HeapUInt` outside 61-bit inline range) and shared `decode_typed_u64_slot` across `_at`, `_unchecked`, and `_data_at`.
- **Verification:**
  - Rust runtime & Cranelift JIT unit tests (`test_typed_words_u64_push_preserves_high_bits_packed_and_unpacked`, `test_cranelift_jit_u64_array_push_preserves_high_bits`) + Simple spec `test/01_unit/lib/common/crypto/u64_array_push_high_bit_spec.spl`.
  - **Status note (`waiting-for: Rust seed rebuild`):** JIT execution fix lives in `src/compiler_rust/**`; `src/lib/common/crypto/argon2.spl:284` workaround stays in tree until the rebuilt Rust seed binary is rolled out.
