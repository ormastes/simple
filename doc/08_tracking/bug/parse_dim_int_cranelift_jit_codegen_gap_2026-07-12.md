# Bug: parse_dim_int Cranelift JIT Codegen Gap

**Status:** OPEN  
**Severity:** Low (fallback to interpreter works)  
**Affects:** Compiled lane only (JIT + Cranelift backend)

## Symptom

The `parse_dim_int` helper function (parses "WIDTH" and "HEIGHT" from "WIDTHxHEIGHT" SHOWCASE_RESOLUTION tokens) fails Cranelift JIT codegen and silently falls back to the interpreter. Function works correctly via interpreter fallback (dry-run parsed 1920x1080 correctly), but the JIT/compiled lane cannot codegen this function.

## Locations

- `examples/06_io/ui/graphics_2d_showcase_gui.spl:50-64`
- `examples/06_io/ui/graphics_2d_showcase.spl:39-53`

## Function Body

```spl
fn parse_dim_int(s: text, default: i32) -> i32:
    val trimmed = s.trim()
    val n = trimmed.len()
    if n == 0:
        return default
    val zero = "0".to_i64()
    var result: i64 = 0
    var i = 0
    while i < n:
        val digit = trimmed.char_at(i).to_i64() - zero
        if digit < 0 or digit > 9:
            return default
        result = result * 10 + digit
        i = i + 1
    return result.to_i32()
```

## Impact

Custom-resolution parsing via `SHOWCASE_RESOLUTION="WxH"` (e.g., "1920x1080") relies on interpreter fallback in JIT lane, degrading performance for dynamic-resolution rendering. The "4k"/"8k" string-match defaults are unaffected (no int parse). Only explicit custom WxH resolution weakens compiled-lane escape hatch for 4K/8K fast paths.

## Suspected Cause

**`trimmed.char_at(i).to_i64() - zero`** — character extraction via method call, conversion chain (char→i64), followed by arithmetic. Cranelift JIT likely lacks direct codegen for this specific char-extraction + conversion pattern.

## Reproduction

```bash
SHOWCASE_RESOLUTION=1920x1080 bin/simple run examples/06_io/ui/graphics_2d_showcase_gui.spl
# Custom resolution parsed via interpreter fallback (JIT codegen fails)
```

## Fix Direction

- Verify which native lanes (LLVM, other backends) are affected.
- Consider inlining char-digit parse loop or using a simpler pattern Cranelift can codegen.
- Alternatively, accept interpreter fallback for custom resolutions (lower priority since default 4K/8K paths unaffected).
