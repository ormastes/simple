# Bug — Interpreter `array.push(u8_literal)` writes 0 instead of value

**Filed:** 2026-05-02 (Wave 13 closeout, W13-E TLS 1.3 PSK connect-flow integration)
**Status:** FIXED 2026-05-10 -- verified by interpreter repro (push(0x2du8) correctly stores 45)
**Severity:** High — silently corrupts byte arrays under interpreter mode; affects any code path that uses `[u8]` literals via `.push(0x..u8)` or `.push(v)` where `v: u8`.

## Symptom

```spl
var a: [u8] = []
a.push(0x2du8)   # expected 0x2d (45), actual 0x00
val v: u8 = 0x2du8
a.push(v)        # expected 0x2d, actual 0x00
a.push((45i64).to_u8())   # works: pushes 45
a.push((45u32 & 0xFFu32).to_u8())   # works: pushes 45
```

Direct `val v: u8 = 0x2du8; v.to_i64()` prints 45 correctly. The bug is specific to **the `.push(...)` write path when the argument is typed `u8`** (literal `0x..u8` or u8 variable). When the argument is constructed via arithmetic-then-`.to_u8()` from u32/i64, it works.

## Repro

```spl
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64
fn main() -> i32:
    val v: u8 = 0x2du8
    print("v as i64={v.to_i64()}")  # 45
    var a: [u8] = []
    a.push(v)
    print("a[0]={rt_bytes_u8_at(a,0).to_i64()}")   # 0 (BUG — should be 45)
    var b: [u8] = []
    b.push((45i64).to_u8())
    print("b[0]={rt_bytes_u8_at(b,0).to_i64()}")   # 45 (works)
    0i32
```

`bin/simple /tmp/repro.spl` → `a[0]=0`, `b[0]=45`.

## Impact

- TLS 1.3 PSK extension byte builders that use `out.push(0x00u8)` / `out.push(0x29u8)` / `out.push(modes[i])` produce wrong wire bytes under interpreter mode. Compile mode may differ.
- `src/os/tls13/handshake13.spl::build_ext_psk_key_exchange_modes` (and any other `0x..u8` literal pushers) silently drops bytes.
- `src/os/tls13/psk.spl::_push_u8(buf, v: u8) → out.push(v)` similarly drops the byte.

## Workaround

Route every u8-write through arithmetic-to-u8:

```spl
out.push((0x2di64 & 0xFF).to_u8())     # works
out.push((v.to_u32() & 0xFFu32).to_u8()) # works for u8 var v
```

W13-E adopted this workaround in `src/os/tls13/tls13.spl` PSK splice helpers
and the `psk_connect_flow_spec` test fixtures. Existing W11-B `psk.spl` and
`handshake13.spl::build_ext_psk_key_exchange_modes` still use the broken
form; their unit-test coverage uses `_seq_n` (which routes through
arithmetic-to-u8) and so didn't catch this.

## Root Cause Analysis (W14 investigation — 2026-05-19)

**The bug was in the READ path, not the WRITE/push path.** The original
"Proposed Fix" hypothesis (push-side method-resolution or value-coercion
mismatch) was incorrect.

### Call chain

1. `0x2du8` literal evaluates in the interpreter to `Value::UInt { value: 45, width: 8 }` —
   confirmed in `src/compiler_rust/compiler/src/interpreter/expr/literals.rs` (line 49:
   `NumericSuffix::U8 => Value::UInt { value: ..., width: 8 }`).

2. `a.push(v)` — `interpreter_method/collections.rs` push arm stores the `Value` as-is into
   `Vec<Value>`. The value `Value::UInt { value: 45, width: 8 }` is stored **correctly**. Push
   path is NOT broken.

3. `rt_bytes_u8_at(a, 0)` → `rt_bytes_u8_at_fn` in
   `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs` → calls
   `interpreter_byte_at(&byte_val)` where `byte_val` is `Value::UInt { value: 45, width: 8 }`.

4. **Bug site: `interpreter_byte_at` (sffi_array.rs lines 17–25).** Before the fix, this
   function had no `Value::UInt` arm. The `Value::UInt` case fell through to the `other`
   branch and returned 0 (either via `unwrap_or(0)` or a bare `_ => 0`).

### Why the workaround worked

`(0x2di64 & 0xFF).to_u8()` performs arithmetic on `Value::Int`, which returns `Value::Int(45)`.
`interpreter_byte_at` had a `Value::Int(n) => n & 0xFF` arm, so 45 was returned correctly.
The workaround bypassed the broken `Value::UInt` arm by producing a different Value variant.

### Fix applied

Added `Value::UInt { value, .. } => (value & 0xFF) as i64` arm to `interpreter_byte_at` in
`sffi_array.rs`. The fixed function is:

```rust
fn interpreter_byte_at(value: &Value) -> i64 {
    let normalized = value.clone().deref_pointer();
    match normalized {
        Value::Int(n) => n & 0xFF,
        Value::UInt { value, .. } => (value & 0xFF) as i64,  // THE FIX
        Value::Union { inner, .. } => interpreter_byte_at(&inner),
        other => other.as_int().map(|n| n & 0xFF).unwrap_or(0),
    }
}
```

### Regression test

`sffi_array.rs` line ~640:
```rust
fn interpreter_byte_at_reads_u8_values_through_wrappers() {
    assert_eq!(interpreter_byte_at(&Value::UInt { value: 0x2d, width: 8 }), 0x2d);
```

## Proposed Fix

~~Investigate `src/compiler_rust/compiler/src/interpreter_extern/...` array-push
dispatch — specifically how `[u8].push(value)` resolves when `value` is
typed `u8` vs the result of `expr.to_u8()`. Likely a method-resolution or
value-coercion mismatch where the typed-u8 path stores 0 (default-init
slot) instead of the argument value.~~

**Resolved** — see Root Cause Analysis above. Fix was in the READ path
(`interpreter_byte_at`), not the push path.

## Related

- `feedback_compile_mode_false_greens.md` — interpreter is supposed to be
  the trusted verification mode; this bug undermines that for byte-builder
  code.
- `feedback_no_coverups.md` — workaround documented here, not silently
  applied.
