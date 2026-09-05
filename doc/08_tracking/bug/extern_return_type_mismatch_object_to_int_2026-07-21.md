# Extern Call Return Type Mismatch: "object to int"

**Date:** 2026-07-21
**Severity:** P1 (blocks rv64 serial_shell_entry compilation)
**Status:** Filed
**Component:** MIR lowering / Semantic analysis

## Verbatim Error

```
error: semantic: type mismatch: cannot convert object to int
```

## Minimal Repro

```spl
extern fn rt_baked_fs_byte(lba: i64, off: i64) -> i64

fn extern_as_return() -> i64:
    rt_baked_fs_byte(0, 0)

fn spl_start():
    val v = extern_as_return()
```

Build:
```bash
bin/simple native-build --backend llvm --target riscv64-unknown-none --emit-object -o /tmp/test.o repro.spl
```

**Result:** `error: semantic: type mismatch: cannot convert object to int`

## Root Cause

When a function returns the result of an `extern fn` call (directly or via a `val`), MIR lowering incorrectly treats the return value as type `object` instead of the declared return type (`i64` in the repro). The error occurs during the inline_call MIR pass (visible via `[F3-DEBUG]` traces).

## Impact

- **NOT arch-specific:** Same error on riscv32 and riscv64 targets
- **Blocks:** `examples/09_embedded/simple_os/arch/riscv64/serial_shell_entry.spl` compilation
- **Workaround exists:** rv32 version works because it calls extern functions inline in `spl_start()`, not via helper functions
- **Pattern:** Any function returning an extern call result fails, including:
  - Direct return: `return extern_call()`
  - Implicit return: `extern_call()` (last expression)
  - Val assignment: `val x = extern_call(); x`

## Why rv32 Works But rv64 Fails

The rv32 `serial_shell_entry.spl` does all FAT32 parsing inline in `spl_start()`:
```spl
val b14_0 = rt_baked_fs_byte(0, 14)
val b14_1 = rt_baked_fs_byte(0, 15)
val reserved = (b14_1 << 8) | b14_0
```

The rv64 version refactored into helper functions:
```spl
fn _u16le(lba: i64, off: i64) -> i64:
    val b1 = rt_baked_fs_byte(lba, off + 1)
    val b0 = rt_baked_fs_byte(lba, off)
    (b1 << 8) | b0
```

This triggers the bug because `_u16le` returns values derived from extern calls.

## Likely Compiler Source Location

Based on error trace (`[F3-DEBUG] inline_call`), the bug is in:
- `src/compiler/60.mir_opt/mir_opt/` - MIR optimization passes, specifically the inline_call pass
- The MIR operand kind system (`MirOperandKind::Copy`) appears to lose type information when copying extern call results

The error originates at semantic/MIR-lowering boundary, where extern call results should retain their declared return type but are instead generalized to `object`.

## Test Cases

All of these currently fail:
```spl
fn test1() -> i64:
    extern_fn()              # direct extern call as return

fn test2() -> i64:
    val x = extern_fn()
    x                       # val wrapping extern result

fn test3() -> i64:
    return extern_fn()      # explicit return with extern call
```

## Action Items

1. Fix MIR lowering to preserve extern function return type through inline_call pass
2. Add regression test: function returning extern call result with --emit-object on riscv64
3. Re-enable rv64 serial_shell_entry helper function pattern after fix
