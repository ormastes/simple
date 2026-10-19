# Seed: u64 values >= 2^63 compared SIGNED; `rt_array_data_ptr` answered 0 for live `[u8]`

- **Filed:** 2026-10-19 (found by the sweep-logic lane, PR #3891)
- **Status:** FIXED in the Rust seed (interpreter + Cranelift JIT), branch
  `work/seed-u64-and-dataptr`. Two related gaps remain OPEN (bottom).
- **Tests:** `src/compiler_rust/compiler/tests/unsigned_semantics_engine_parity.rs`
  (interpreter AND JIT on the same source), and
  `test/01_unit/bugs/seed_unsigned/{seed_unsigned_semantics_spec,seed_u8_data_ptr_spec}.spl`.

## Bug 1 — unsigned values became signed

A `u64` is carried as an `i64` bit pattern, so a value >= 2^63 is negative as
`i64`. It must still compare/divide/shift unsigned where the static type is
unsigned. It did not:

| engine | site | effect |
|---|---|---|
| interpreter | module-level `val X: u64 = ...` in an IMPORTED module (`evaluation_helpers.rs` Let/Const/Static evaluated the initializer and dropped the annotation) | `VMM_KERNEL_SPACE_START` imported as `Int(-140737488355328)`; `0x7FF0 < it` false; every user page walk in `vmm_copyin_spec` failed |
| interpreter | `const X: u64` / `static` anywhere (`node_exec.rs`) | same, same module |
| interpreter | typed `val` inside a closure block — every spec `it` body (`block_execution.rs`, two Let arms) | `val big: u64 = 0xFFFF...F8` compared negative |
| interpreter | declared `-> u64` returns (`function_exec.rs`) | `p < kstart_fn()` false |
| JIT | integer literal `ConstInt` always typed `i64` in `build_vreg_types` | `0xFFFF...F8u64 > 5u64` false; `0x8000...u64 / 2u64`, `>> 60u64`, `% 10u64` signed |
| JIT | `Div`/`Mod` chose `udiv`/`urem` from the LHS only | `0xFFFF...FFu64 / three_u64` = 0 |

Fix: one helper, `coerce_to_declared_type` (`interpreter/node_exec.rs`), applied
at every interpreter binding site that has a declared type. JIT: a `u64`
literal with bit 63 set is followed by a zero-cost `Cast I64 -> U64` so its
vreg is typed unsigned (literals below 2^63 are identical under either
signedness and stay a bare `ConstInt`, so constant-pattern consumers are
untouched); `Div`/`Mod` are unsigned when EITHER operand is unsigned, the rule
ordering comparisons already used. u32/u16/u8 values are always non-negative
as `i64`, so signed ops on them were already correct; wraparound rows for u32
are in the parity test.

## Bug 2 — `rt_array_data_ptr` returned 0 for a live `[u8]`

| representation | interpreter before | interpreter after | native (JIT) |
|---|---|---|---|
| packed `ByteArray` (`rt_bytes_alloc`, slices of it) | real ptr | real ptr | real ptr |
| `var x: [u8] = []` + push / `out = out.push(..)` | **0** (boxed `Array`) | real ptr (binding is packed) | real ptr |
| `val x: [u8] = [1u8, 2u8]` | **0** | real ptr | real ptr |
| empty `[u8]` binding | **0** | non-zero (packed, empty) | non-zero |
| untyped boxed array of `u8` (struct-field `[]` + push, a bare literal argument) | **0** | **error** naming the cause | slot pointer (see open gap) |
| non-`u8` boxed array (`[i64]`, `[text]` via a generic decl) | 0 | 0 = "no packed byte storage" | slot pointer |

The interpreter stored every `[u8]` built from `[]` as boxed `Value::Array`,
which has no contiguous bytes. `[u8]`-typed bindings now become packed
`Value::ByteArray` (element reads already yield `u8`, so reads are unchanged).
A non-empty boxed array that is provably `u8` now fails loudly instead of
answering 0; 0 is documented as "empty-and-boxed or not a byte array" only.
`theme_notification_protocol_spec` 3/4 -> 4/4.

## OPEN

1. **Unsuffixed literals >= 2^63 are `i64` before any annotation applies.**
   `val MASK: u64 = 0xFFFF_FFFF_FFFF_FFFF >> 4` is an arithmetic shift of -1
   (both engines), so `MASK` is `u64::MAX`, not `0x0FFF...`. The lexer
   (`parser/src/lexer/numbers.rs:69-70`) parses such a literal as `u64` and
   stores it untyped. Typing it `u64` is a language change: 1,087 unsuffixed
   literals >= 2^63 exist under `src/`, several in `i64`-typed hash code
   (`var h: i64 = 0xCBF29CE484222325`). Workaround: write the `u64` suffix.
2. **Native slot-layout `[u8]`.** A struct-field `[]` literal builds a
   slot-layout array (8-byte tagged elements); native `rt_array_data_ptr`
   returns the slot pointer, so a byte reader sees `5 << 3 = 40` for byte 5.
   Non-zero but wrong. The runtime cannot tell `[u8]` from `[u64]` there; the
   fix belongs at construction (type the literal) — see
   `jit_hoisted_u8_data_ptr_ignores_slot_layout_2026-10-19.md`.
3. `vmm_copyin_spec` still fails 3/18 after this fix, for an unrelated
   pre-existing reason now reachable: inside `vmm_copy.spl` the imported
   `PTE_*` names resolve to `os.kernel.types.bitfield`'s same-named bit
   INDICES (`PTE_HUGE_PAGE = 7`). See
   `interp_vmm_copy_pte_constants_resolve_to_bitfield_indices_2026-10-20.md`.
