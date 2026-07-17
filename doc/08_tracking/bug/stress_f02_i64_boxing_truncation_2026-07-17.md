# Cert stress f02: large i64 literals silently truncate in compiled/JIT `print`

- **Date:** 2026-07-17
- **Severity:** P1 (silent wrong result in compiled code, not an error/crash)
- **Status:** FIXED (STRESS lane, 2026-07-17). Root-fixed in the Rust seed
  (`src/compiler_rust`). Verified against the seed binary; see Verification
  below. The self-hosted pure-Simple compiler (`src/compiler`) was not
  audited for the analogous defect — file separately if it reproduces there.
- **Area:** MIR lowering of `print`/`println`/`eprint`/etc. numeric args
  (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs`) and
  the runtime tagged-value boxing scheme
  (`src/compiler_rust/runtime/src/value/core.rs`).
- **Source:** `test/cert/stress/findings/f02_bigint_literal_codegen.spl`
  (originally documented by the cert stress-suite salvage,
  `scripts/check/cert/stress-suite.shs`).

## Symptom

```
fn main():
    print(9223372036854775807)   # i64::MAX
```

- Cranelift JIT / compiled backend (`simple run`, default execution mode):
  printed `-1`.
- `print(4611686018427387904)` (2^62): printed `0`.
- Tree-walking interpreter mode (`SIMPLE_EXECUTION_MODE=interpret`): always
  printed the correct value — the interpreter uses a native Rust `Value`
  enum, not the tagged `RuntimeValue`, so it never hit this path.
- Literals under ~2^60 (e.g. `1000000000000`) were unaffected in both modes.

## Root cause

`RuntimeValue` (`runtime/src/value/core.rs`) packs a tag into the low 3 bits
of a 64-bit word: `(payload << 3) | tag`, so only a **signed 61-bit** payload
round-trips (`[-2^60, 2^60)`). This is a documented, deliberate tradeoff (see
the type's doc comment: "Only 61-bit signed integers can be stored directly.
Larger integers would need heap allocation") — but no heap-boxed fallback
exists, so anything outside that range that DOES get boxed silently loses its
top 3 bits.

`print`/`println`/`eprint`/etc. box every numeric argument into a
`RuntimeValue` before calling the shared runtime print routine
(`lowering_expr_builtin.rs`, the `"print" | "println" | ...` arm), via
`MirInst::BoxInt` (`raw << 3`, see
`compiler/src/codegen/instr/mod.rs:1330`). For `i64::MAX` = `0x7FFF...FFFF`,
`<< 3` drops the top 3 (all-`1`) bits, producing `0xFFFF...FFF8`; the runtime
print path unboxes via `(bits as i64) >> 3` (arithmetic shift), which
sign-extends that back to `-1`. For `2^62` = `0x4000...0000`, the same `<< 3`
shifts the set bit past bit 63 entirely, producing `0`.

This exact class of bug was already known and partially fixed for **unsigned**
64-bit values: `rt_raw_u64_to_string` (added earlier, see its doc comment)
lets `print`/etc. stringify a raw `u64`-typed argument directly, bypassing
the lossy box. `u64` args were special-cased in
`lowering_expr_builtin.rs`'s print-arg loop; the analogous case for `i64` —
the *default* `int` type, `TypeId::I64` — was simply missing, so `int`
literals near `i64::MIN`/`i64::MAX` still went through the lossy boxed path.

## Fix

Added `rt_raw_i64_to_string(raw: i64) -> RuntimeValue` (mirrors
`rt_raw_u64_to_string`, just `raw.to_string()` — no unboxing needed since the
value is already an unboxed native i64) and extended the print-arg
special-case in `lowering_expr_builtin.rs` to route `TypeId::I64` (not just
`TypeId::U64`) through the raw-to-string bypass instead of `BoxInt`.

Files changed:
- `src/compiler_rust/runtime/src/value/sffi/io_print.rs` — new
  `rt_raw_i64_to_string` + a unit test
  (`test_raw_i64_to_string_preserves_values_outside_61bit_box_range`).
- `src/compiler_rust/runtime/src/value/mod.rs`,
  `src/compiler_rust/runtime/src/lib.rs` — re-export + symbol-table keep-alive
  (mirrors the existing `rt_raw_u64_to_string` wiring).
- `src/compiler_rust/compiler/src/elf_utils.rs`,
  `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`,
  `src/compiler_rust/common/src/runtime_symbols.rs` (×2 call sites) —
  register the new runtime symbol alongside `rt_raw_u64_to_string`.
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs` —
  route `TypeId::I64` print args through `rt_raw_i64_to_string`; narrowed the
  `needs_int_boxing` match to drop `I64` (now unreachable there, handled
  earlier).

## Verification

```
cd src/compiler_rust && cargo build --release
SIMPLE_BIN=src/compiler_rust/target/release/simple \
  sh scripts/check/cert/stress-suite.shs
```

Before: `finding f02_bigint_literal_codegen.spl -> OK rc=0 got=[-1]`
After:  prints `9223372036854775807` (exact match), moved from the
findings/README defect list into the CORE gate as a pinned `valid_case`.
Also verified small ints are unaffected: `print(42)` still prints `42`,
`2^62` now prints `4611686018427387904` correctly, and `i64::MIN`
(`-9223372036854775808`) prints correctly too.

A baseline A/B rebuild (reverting just these 7 files back to pre-fix
content, rebuilding, and re-running `cargo test -p simple-compiler --lib`)
was done to rule out this change causing any of the ~257 pre-existing,
unrelated test failures in that suite (baseline: 258 failed; fixed: 257
failed — the 3 tests that differed between runs were independently
confirmed to be parallel-execution-order flaky, not caused by this diff, by
rerunning each in isolation with `--test-threads=1` both with and without
the fix applied).

## Known remaining scope (not fixed, explicitly out of scope for this fix)

This fix only covers the `print`/`println`/`eprint`/etc. **argument
boundary**. The general `RuntimeValue`/`ANY`-boxing scheme
(`MirInst::BoxInt` used for arrays of `Any`, `Any`-typed function
parameters, dict values, etc.) still silently truncates any raw i64/u64
outside `[-2^60, 2^60)` wherever it flows through `BoxInt` by a path other
than a direct print-call argument. A full fix would need a heap-boxed-int
fallback (new `HeapObjectType`, `UnboxInt` update to dereference it) — out of
scope here per "never over-engineer"; this narrow, precedented fix matches
how the codebase already chose to handle the identical u64 case.
