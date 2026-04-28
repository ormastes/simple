# Bug: enum field destructuring drops i64 values (returns 0)

**Date:** 2026-04-28
**Severity:** correctness — silently drops integer fields when destructuring enum variants
**Discovered by:** TLS live-lane bisection (`/dev tls_live_bug_fix_restart`, D4/D9/D10 fix attempt)

## Symptom

In compile-mode (Cranelift bare-metal `x86_64-unknown-none`), constructing an enum variant with an integer field and then destructuring it loses the field's value.

```
enum RecordResult:
    Ok(content_type: i64, data: [u8])
    Err(msg: text)

# Inside _record_unpack_inner_with_len:
val real_content_type: i64 = _u8_at(inner, cursor).to_i64()
serial_println("inside: real_ct={real_content_type}")  # prints 22
RecordResult.Ok(real_content_type, data)               # construct

# At test site:
if val RecordResult.Ok(ct, dt) = res:
    # ct reads as 0, but inner unpack proved real_ct=22
```

Same behavior with named-field construction (`Ok(content_type: ..., data: ...)`) and with `u8` field type. The `text` field of `Err(msg: text)` works correctly — only integer fields are affected.

## Reproduction

Verified empirically via `[BISECT-UNPACK]` probe in `_record_unpack_inner_with_len`:

```
[BISECT-UNPACK] inner_len=6 cursor=5 real_ct=22
[DBG] D4 ct4=0 dt4.len()=5
```

inner unpack has `real_ct=22` (= 0x16, the encoded TLS content type), but the test's `ct4` after destructuring is 0. The `data` field (a `[u8]`) destructures correctly — `dt4.len()=5` and the bytes are right.

## Root cause — confirmed (2026-04-28)

### ct=0 trace (multi-field variant destructuring)

1. **`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` ~line 888** — PRIMARY BUG (outside `mir/lower/`+`codegen/instr/` scope)

   For `if val RecordResult.Ok(ct, dt) = res` with `payload_patterns.len() > 1`, the code constructs:
   ```rust
   let payload_expr = HirExpr {
       kind: HirExprKind::BuiltinCall { name: "rt_enum_payload", args: [...] },
       ty: binding_ty,   // BUG: binding_ty = I64 for the `ct` field
   };
   ```
   `payload_expr.ty` must be `TypeId::ANY` for multi-field variants, because `rt_enum_payload` returns the wrapper array (a heap pointer), not the field value directly.

2. **`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs`** — in scope

   `lower_builtin_call_expr` special-cases `rt_enum_payload`. When `expr_ty = I64`, it sets `needs_int_unbox = true` and emits `UnboxInt` on the raw result:
   ```rust
   // expr_ty = I64 → UnboxInts the wrapper-array heap pointer → garbage integer
   block.instructions.push(MirInst::UnboxInt { dest: unboxed, value: raw_result });
   ```
   For a multi-field variant, this produces a garbage integer instead of the array pointer.

3. **`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs`** — in scope

   `lower_index_expr` then calls `rt_index_get(garbage_int, ENCODE_INT(0))`. Inside the runtime:
   - `IS_HEAP(garbage_int)` fails → returns `NIL_VALUE = 3`
   
   `lower_index_expr` applies another `UnboxInt` based on `expr_ty = I64`:
   - `DECODE_INT(3) = 3 >> 3 = 0` → **ct = 0**

4. **`text` field works** because it is a heap pointer: the `IS_HEAP` check in `rt_index_get` succeeds and the stored pointer is returned directly, so no tag-path damage occurs.

### Secondary bug — in scope

**`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs` ~lines 115–130** — multi-field enum variant construction

When constructing a multi-field variant, integer args are pushed to the wrapper array without `BoxInt`:
```rust
for arg in &arg_regs {
    // BUG: no BoxInt inserted here for integer args
    block.instructions.push(MirInst::Call {
        dest: None,
        target: CallTarget::from_name("rt_array_push"),
        args: vec![array_reg, *arg],
    });
}
```
The `rt_array_push_handle` runtime comment explicitly states: "Values now arrive TAGGED from the compiler: .push(expr): MIR BoxInt inserted in lowering_expr.rs for integer args." The enum construction path skips this tagging, so integer fields are stored untagged — but this bug is masked by the primary bug above (ct=0 happens before array indexing even gets a chance to read a stored value).

### Fix plan

Fix order matters:

1. **`stmt_lowering.rs` ~line 888**: For `payload_patterns.len() > 1`, set `payload_expr.ty = TypeId::ANY` so `lower_builtin_call_expr` does not insert `UnboxInt` on the wrapper-array pointer.

2. **`lowering_expr_builtin.rs`**: Guard the `rt_enum_payload` unbox: only apply `needs_int_unbox` when the call-site type is actually a scalar (single-field variant). When the payload is a wrapper array, the type should be `ANY`/opaque.

3. **`lowering_expr_call.rs` ~lines 115–130**: Insert `MirInst::BoxInt` before each `rt_array_push` call for integer-typed enum construction args (mirrors what `lower_assign_stmt` does for regular assignments).

### Fix attempt (2026-04-28) — INCOMPLETE

Fixes #1 and #3 were applied in tree:
- `stmt_lowering.rs:893-896` — `payload_expr_ty = TypeId::ANY` when `payload_patterns.len() > 1`.
- `lowering_expr_call.rs:121-160` — `MirInst::BoxInt` inserted before `rt_array_push` for arg types in {I8/I16/I32/I64/U8/U16/U32/U64/BOOL}.

Verification: rebuilt with `cargo build`, force-rebuilt the QEMU kernel, switched D4 in `tls_unit_entry.spl` from `rt_tls13_record_decrypt_compact` back to enum destructuring (`if val RecordResult.Ok(ct4, dt4) = dec4`). Result: **D4 still produces `ct4=0`**. Live gate dropped 36/0 → 35/1.

Reverted D4 to compact-API; live gate restored to 36/0.

**The bug is deeper than the traced 4-step path.** Possible additional sources:
- Step 2 (`lowering_expr_builtin.rs` `rt_enum_payload` UnboxInt) may still trigger something else even when `expr_ty=ANY` (e.g., the `tagged_vregs` insertion at line 33 with downstream Store/Load propagation).
- The runtime `rt_array_push_handle` may not actually preserve tagging across the array slot despite the comment.
- `rt_index_get`'s `ENCODE_INT(idx)` may interact unexpectedly with our BoxInt'd values during lookup.
- A separate path in MIR lowering may still insert `UnboxInt` between construction and destructuring.

A future investigation should probe between each step empirically (print intermediate VReg values during run) instead of only static-tracing.

The live gate is green via the `rt_tls13_record_decrypt_compact` workaround. The compiler partial fix remains in tree; reverting it is unnecessary because it doesn't regress anything (live gate is 36/0 with the workaround).

## Workaround in tree (2026-04-28)

For the TLS record-decrypt path, added a parallel API `rt_tls13_record_decrypt_compact` (C extern in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`) that returns the content_type as byte[0] of a `[u8]` runtime array, with the data bytes following. Test code calls this directly via `rt_bytes_u8_at(res, 0)` to read content_type instead of going through the enum.

`src/os/tls13/record13.spl` keeps the `RecordResult` enum for hosted-mode and for callers that don't need the integer field. The `i64` field type was a probe — `u8` had the same bug.

## Why root-cause fix matters

Any compile-mode code path that returns integer payloads through enum variants silently zeroes the integer. This is broad:
- `Result<T, E>` style enums with integer payloads
- Status-code enums
- AEAD/crypto Result types
- Any error enum carrying an error code

The workaround pattern (compact `[u8]` with sentinel byte) doesn't generalize cleanly to multi-field structures.

## Investigation summary (2026-04-28)

Investigation confirmed the root cause. Key files checked:

- `src/compiler_rust/compiler/src/codegen/instr/pattern.rs` — `compile_pattern_bind`: dead code for `if val` patterns; `MirInst::EnumPayload` has zero emission sites in `mir/lower/`. Not the bug.
- `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` ~line 888 — **primary bug** (`payload_expr.ty = binding_ty` for multi-field variants). Outside `mir/lower/`+`codegen/instr/` scope.
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs` — `rt_enum_payload` unbox guard is missing the multi-field check. In scope.
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs` ~lines 268–430 — `lower_index_expr` applies a second `UnboxInt` using `expr_ty`. In scope.
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs` ~lines 115–130 — missing `BoxInt` before `rt_array_push` for integer enum construction args. In scope (secondary bug).
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` — runtime tag macros: `ENCODE_INT(v) = (v << 3) | 0`, `DECODE_INT(v) = v >> 3`, `NIL_VALUE = 3`. `rt_array_get` returns stored `RuntimeValue`; `rt_index_get` calls `DECODE_INT(idx)` first; `IS_HEAP` guard in array access.
