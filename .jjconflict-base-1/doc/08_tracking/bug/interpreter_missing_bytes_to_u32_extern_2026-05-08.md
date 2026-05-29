# Bug — Interpreter missing `bytes_to_u32_le`/`bytes_to_u32_be` externs

**Filed:** 2026-05-08 (debug format library test failures)
**Status:** FIXED 2026-05-10 -- verified by interpreter repro (all bytes_to_u16/u32/u64 le/be externs registered and returning correct values)
**Severity:** High — blocks any interpreter-mode code using `BinaryReader.read_u16()`, `read_u32()`, `read_u64()`, and any code that imports modules calling these methods.

## Symptom

```
semantic: unknown extern function: bytes_to_u32_le
```

When calling `BinaryReader.read_u32(ByteOrder.LittleEndian)` in interpreter mode, the interpreter cannot find the `bytes_to_u32_le` extern function. This also causes module-level import failures for any `.spl` file that calls `read_u32` — even if the test code itself doesn't use it.

## Root Cause

`BinaryReader.read_u32()` in `src/lib/nogc_sync_mut/binary_io.spl:196` calls `bytes_to_u32_le(bytes)`, which is an extern function. The Rust interpreter (`src/compiler_rust/`) does not register this extern in its extern function table.

**Working:** `BinaryReader.read_u8()` — doesn't use byte-conversion externs.
**Broken:** `read_u16()`, `read_u32()`, `read_u64()`, `read_i16()`, `read_i32()`, `read_i64()` — all use `bytes_to_u*_le/be` externs.

## Affected Modules

Any module importing and calling `BinaryReader.read_u16/u32/u64` will fail in interpreter mode:

- `src/lib/nogc_sync_mut/debug/formats/msf_parser.spl` — uses `read_u32` for MSF header parsing
- `src/lib/nogc_sync_mut/debug/formats/dwarf_line_program.spl` — uses `read_u16/u32` for DWARF line headers
- `src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl` — uses `read_u32` for section parsing
- Any test spec that imports these modules

## Workaround

For interpreter-mode tests, avoid `BinaryReader.read_u32()`. Use manual byte reading:

```spl
fn read_u32_le(data: [u8], offset: i64) -> i64:
    val b0 = data[offset] as i64
    val b1 = data[offset + 1] as i64
    val b2 = data[offset + 2] as i64
    val b3 = data[offset + 3] as i64
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
```

## Proposed Fix

Register `bytes_to_u32_le`, `bytes_to_u32_be`, `bytes_to_u16_le`, `bytes_to_u16_be`, `bytes_to_u64_le`, `bytes_to_u64_be` in the interpreter extern function table. Likely in `src/compiler_rust/compiler/src/interpreter_extern/`.

## Resolution

**Fixed in:**
- `fe621f0056` — `perf(interp): HashMap extern dispatch — O(1) lookup for 1038 functions`: Initial HashMap dispatch table registering all six `bytes_to_u*_{le,be}` externs.
- `fca3f29b05` — `perf(interpreter): replace 1080-arm extern dispatch match with HashMap lookup`: Consolidated slow-path, confirmed all six names remain in the table.

**Implementation in** `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs`:
- `bytes_to_u32_le_fn` / `bytes_to_u32_be_fn` — accept `[u8]` array (matches `bytes_to_u32_le(bytes)` call in `binary_io.spl:196`)
- `bytes_to_u16_le_fn` / `bytes_to_u16_be_fn` — accept two individual `u8` args (matches `bytes_to_u16_le(b0, b1)` call in `binary_io.spl:160`)
- `bytes_to_u64_le/be` — pure-Simple implementations in `binary_io.spl` (no extern needed)

All six names are registered in `init_dispatch_table()` in `mod.rs`. The `simple-compiler` crate compiles cleanly (`cargo check -p simple-compiler` passes).

## Related Bugs

- `interpreter_bang_unwrap_member_access_2026-05-08.md` — discovered during same test session
- `aes_extern_expect_byte_array_u8_reject_2026-05-02.md` — similar missing extern pattern
