# Interpreter `Value::UInt` missing method dispatch — breaks every `u8.to_u32()`/`.to_i64()`/`.to_u64()` site

Date: 2026-05-01 (filed during W6 zstd non-RLE seq-tables lane)
Status: **OPEN — blocks every Zstd, Huffman, FSE, range-coder, and TLS spec that touches `u8` payload bytes via `.to_u32()` / `.to_i64()` / `.to_u64()`.**

## Symptom

Every spec call shaped like `data[i].to_i64()`, `data[i].to_u32()`,
`data[i].to_u64()` fails at semantic time with:

```
semantic: method `to_u32` not found on type `u8` (receiver value: <byte>)
semantic: method `to_i64` not found on type `u8` (receiver value: <byte>)
semantic: method `to_u64` not found on type `u8` (receiver value: <byte>)
```

This breaks (verified empirically 2026-05-01 evening):

| Spec | Status before | Status now |
|---|---|---|
| `test/unit/lib/common/zstd_bits_spec.spl` | PASS (assumed) | **3/4 FAIL** |
| `test/unit/lib/common/zstd_fse_weights_spec.spl` | 6/6 PASS (W5-E) | **1/6 PASS** |
| `test/unit/lib/common/zstd_compressed_block_spec.spl` | 3/7 PASS | **0/7** |
| `test/unit/lib/common/zstd_sequence_header_spec.spl` | 5/5 PASS | **0/5** |
| `test/unit/lib/common/zstd_sequence_fse_tables_spec.spl` | 3/3 PASS | **0/3** |
| `test/unit/lib/common/zstd_sequence_fse_execution_spec.spl` | 15/15 PASS (assumed) | **2/15** |

The two passing cases in `zstd_sequence_fse_execution_spec.spl` are the
two that don't drive a `[u8]` through `.to_u32()` (they exercise pure
encoder helpers). The pattern is consistent across all failing cases.

## Root cause

Commit `2ec2342969 fix(interp): u32/u8/u16/u64 wrap arithmetic via
Value::UInt with width tag` introduced a new interpreter value variant:

```rust
Value::UInt { value: u64, width: u8 }   // src/compiler_rust/compiler/src/value.rs
```

…and migrated literals, casts, and `var x: u8 = …` annotations to
produce `Value::UInt` so wrap arithmetic at width works for the LZMA
range coder. However:

- `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
  was NOT updated. The match arms at lines 338 (`Value::Int(n) =>
  match method`) and 355 (`Value::Float(f) => match method`) handle
  `to_u32`/`to_i64`/`to_u64`/etc., but there is **no `Value::UInt {
  value, width } => match method` arm**.

- Result: any `u8` byte read out of a `[u8]` array via
  `array[i]` now returns a `Value::UInt { width: 8 }`. Calling
  `.to_u32()` / `.to_i64()` / `.to_u64()` on it falls through every
  match arm and hits the "method not found on type u8" diagnostic at
  line 507 of `method_dispatch.rs`.

The bug is small and mechanical (add a `Value::UInt` arm that mirrors
the `Value::Int` arm, but treating the stored `value: u64` as the
source — modular wrap from u64 → target width is already implemented in
`cast_int_to_numeric` once you supply an i64 view, which `as_int()`
already provides per the commit message).

## Reproduce

```bash
cd /home/ormastes/dev/pub/simple
bin/simple test/unit/lib/common/zstd_bits_spec.spl
# or any spec listed in the table above.
```

## Fix sketch (do not act in this lane)

1. In `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`,
   add a `Value::UInt { value, width }` arm parallel to the existing
   `Value::Int(n)` arm. Map `to_i64`/`to_u32`/`to_u64`/etc. through the
   same `cast_int_to_numeric` (signed-aware) or a new
   `cast_uint_to_numeric` helper that takes the raw u64 plus source
   width. `to_string` / `to_text` should print the unsigned decimal.
2. Mirror the change anywhere else `Value::Int` is exhaustively matched
   for method dispatch (e.g. comparison, sort, pretty-print). The
   `value_bridge.rs` site at line 288 already handles UInt; reusing
   that pattern gives the right semantics.
3. Add `test/unit/compiler/interpreter_uint_method_dispatch_spec.spl`
   covering each `to_*` method on every width (u8/u16/u32/u64) plus
   `abs` (n/a — UInt is non-negative) and `to_string`.

## Impact on W6 non-RLE sequence-tables lane

The W6 task as briefed
(`doc/03_plan/agent_tasks/common_compression_framework.md` line 35,
`zstd.spl:324`) was framed as "non-RLE sequence-table decode missing".
**Empirical re-investigation 2026-05-01 evening shows the framing is
stale on three counts:**

1. **`_zstd_parse_single_sequence_table` (`zstd.spl` line 367) already
   handles modes 0/1/2/3** — predefined, RLE, FSE-compressed, and
   Repeat_Mode (mode 3 uses `previous_table` from the
   `ZstdSequenceTableHistory` argument). The `UnsupportedFeature("zstd
   non-rle sequence tables are not supported")` error at line 354
   belongs to a leftover stub `_zstd_parse_rle_sequence_tables` that is
   **no longer called** from the main dispatcher; the live path is
   `_zstd_parse_sequence_tables` at line 390 which calls the
   mode-aware single-table function.

2. **The dispatcher (`zstd.spl` lines 1525-1531) already wires
   `_zstd_parse_sequence_tables` and `_zstd_decode_fse_sequences`
   end-to-end** with `sequence_table_history` flowing through from
   `dictionary_state.sequence_history` (line 1478) and back into
   `next_sequence_table_history` (line 1529).

3. **W5-E's MSB reader `ZstdMsbBackwardBits` is currently used only
   by `_zstd_parse_fse_compressed_weights`.** The
   `_zstd_decode_fse_sequences` path still uses the LSB-first
   `ZstdBackwardBits`. Per RFC 8478 Annex A the FSE state stream
   for sequence decoding **also** needs MSB-first, so a second-step
   migration is plausible — but cannot be empirically verified
   right now because the UInt-method-dispatch bug above prevents
   any spec from reaching that code path.

The honest current state: the verify-report `zstd.spl:324` FAIL line
points at a stub error message that is no longer reachable (the live
path returns an `UnsupportedFeature("fse sequence execution")` from
deeper inside, when `_zstd_decode_fse_sequences` runs but hits the
known offset-code-31 gate). When the UInt-dispatch bug above is
fixed, the proper next step is:

- Re-run the existing seq-tables/seq-exec specs to learn the current
  factual fail pattern (likely host-zstd byte-exact mismatch via
  LSB/MSB order mismatch, mirroring W5-E's Huffman-weight bug).
- If LSB/MSB confirmed, swap `ZstdBackwardBits` → `ZstdMsbBackwardBits`
  in `_zstd_read_sequence_bits`, `_zstd_read_sequence_state`,
  `_zstd_advance_sequence_state`, `_zstd_decode_fse_sequences`.
- File a deferred bug doc tracking the `_zstd_parse_rle_sequence_tables`
  dead-code stub for cleanup.

## Verify report

`doc/09_report/verify_common_compression_framework.md` line 13 stays
**FAIL** with a reference to this bug doc. The implementation surface
exists and is dispatched correctly; the apparent failure is not in the
zstd code but in the interpreter's inability to dispatch the `to_*`
family of methods on `Value::UInt` after the W5-I wrap-arithmetic fix.

## Out of scope for this lane (W6)

- Patching `method_dispatch.rs` is a compiler-team concern (tracked
  under doc/08_tracking/bug/interpreter_*.md series, several recent
  open) not a compress-codec concern.
- Re-flipping zstd.spl:324 to PASS requires the UInt fix to land
  first, then a fresh empirical pass over the live FSE-state path.

## References

- `doc/08_tracking/bug/bug_zstd_fse_huffman_weight_kraft_2026-05-01.md`
  — W5-E's MSB-first fix template (close cousin of the next zstd step).
- `doc/08_tracking/bug/interpreter_u32_wrap_subtraction_2026-05-01.md`
  — original commit `2ec2342969` motivation; this bug is the unsigned
  follow-on.
- `doc/03_plan/agent_tasks/common_compression_framework.md` line 35.
- `doc/09_report/verify_common_compression_framework.md` line 13.
