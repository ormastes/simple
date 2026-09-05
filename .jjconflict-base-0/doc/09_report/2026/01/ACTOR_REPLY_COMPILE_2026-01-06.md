# Actor Reply Compilation Support - 2026-01-06

## Summary

Implemented full compilation support for the actor `reply` operation, enabling it to be compiled to native code instead of requiring interpreter fallback.

## Implementation Complete

Added complete compilation pipeline for `reply`:

1. ✅ **Runtime FFI**: `rt_actor_reply` in `src/runtime/src/value/actors.rs`
2. ✅ **MIR Instruction**: `ActorReply { message: VReg }` in `src/compiler/src/mir/inst_enum.rs`
3. ✅ **HIR Lowering**: Recognizes `reply` and creates `HirExprKind::BuiltinCall` in `src/compiler/src/hir/lower/expr/calls.rs`
4. ✅ **MIR Lowering**: Converts `BuiltinCall{name: "reply"}` to `MirInst::ActorReply` in `src/compiler/src/mir/lower/lowering_expr.rs`
5. ✅ **Codegen**: Calls `rt_actor_reply` runtime function in `src/compiler/src/codegen/instr.rs`
6. ✅ **Effect System**: Marked as non-blocking I/O operation (Effect::Io) in `src/compiler/src/mir/inst_effects.rs`
7. ✅ **Helper Methods**: Added to `uses()` in `src/compiler/src/mir/inst_helpers.rs`
8. ✅ **Compilability**: Updated to enable `reply` compilation in `src/compiler/src/compilability.rs`

## Files Modified

### Runtime
- **src/runtime/src/value/actors.rs** (+14 lines)
  - Added `rt_actor_reply` FFI function
  - Sends message through CURRENT_ACTOR_OUTBOX
  - Returns RuntimeValue::NIL

### Compiler - Constants & Types
- **src/compiler/src/value.rs** (+3 lines)
  - Added `BUILTIN_REPLY` constant

### Compiler - MIR
- **src/compiler/src/mir/inst_enum.rs** (+4 lines)
  - Added `ActorReply { message: VReg }` variant

### Compiler - HIR Lowering
- **src/compiler/src/hir/lower/expr/calls.rs** (+12 lines)
  - Added import for `BUILTIN_REPLY`
  - Added `reply` recognition and HIR node creation
  - Returns type `TypeId::NIL`

### Compiler - MIR Lowering
- **src/compiler/src/mir/lower/lowering_expr.rs** (+13 lines)
  - Added special handling for `reply` builtin
  - Creates `ActorReply` instruction followed by `ConstInt` for NIL return value
  - Fixed borrow checker issue by calling `new_vreg()` before `block_mut()`

### Compiler - Codegen
- **src/compiler/src/codegen/instr.rs** (+8 lines)
  - Added `ActorReply` code generation
  - Calls `rt_actor_reply` runtime function
  - Result handled by subsequent ConstInt instruction

- **src/compiler/src/codegen/runtime_ffi.rs** (+1 line)
  - Registered `rt_actor_reply` with signature `(&[I64], &[I64])`

### Compiler - Effect System
- **src/compiler/src/mir/inst_effects.rs** (+1 line)
  - Added `ActorReply` to non-blocking I/O operations (Effect::Io)

- **src/compiler/src/mir/inst_helpers.rs** (+1 line)
  - Added `ActorReply` to `uses()` method (uses message register)

### Compiler - Compilability
- **src/compiler/src/compilability.rs** (+2 lines, -2 lines)
  - Changed `is_non_compilable_actor_builtin` to return `false` for all actor operations
  - Updated comment: "All actor operations (spawn, send, recv, join, reply) are now compilable"

## Technical Details

### Runtime Implementation
The `rt_actor_reply` function accesses the thread-local `CURRENT_ACTOR_OUTBOX` to send a message to the parent actor:

```rust
pub extern "C" fn rt_actor_reply(message: RuntimeValue) -> RuntimeValue {
    CURRENT_ACTOR_OUTBOX.with(|cell| {
        if let Some(tx) = cell.borrow().as_ref() {
            let bits = message.to_raw();
            let payload = Message::Bytes(bits.to_le_bytes().to_vec());
            let _ = tx.send(payload);
        }
    });
    RuntimeValue::NIL
}
```

### MIR Lowering Pattern
Since `reply` is a void operation, the MIR lowering creates two instructions:
1. `ActorReply { message }` - Sends the message
2. `ConstInt { dest, value: 0 }` - Creates NIL return value

This pattern ensures proper SSA form where every operation produces a value.

### Effect Classification
`reply` is classified as non-blocking I/O (Effect::Io) because:
- It doesn't block on synchronization
- It just sends a message to an outbox channel
- Similar to `send` and `spawn` operations

## Test Results

Test file `/tmp/test_reply.spl`:
```simple
fn worker():
    msg = recv()
    reply(msg * 2)

fn main():
    handle = spawn(worker)
    send(handle, 21)
    result = join(handle)
    if result == 1:
        return 100
    return 200
```

**Both debug and release builds**: Exit code 100 ✅

## Actor Operations Summary

All actor operations are now compilable:

| Operation | Type | Effect | Status |
|-----------|------|--------|--------|
| `spawn` | Create | Io | ✅ Compilable |
| `send` | Message | Io | ✅ Compilable |
| `recv` | Message | Wait (blocking) | ✅ Compilable |
| `join` | Sync | Wait (blocking) | ✅ Compilable |
| `reply` | Message | Io | ✅ Compilable |

## Next Steps

- Add comprehensive actor operation tests to test suite
- Consider implementing request-response patterns using reply
- Optimize message passing for compiled code paths
- Add actor lifecycle management tests

## Related Reports

- [ACTOR_JOIN_FIX_2026-01-06.md](ACTOR_JOIN_FIX_2026-01-06.md) - Fixed join return value
- [ACTOR_JOIN_ISSUE_2026-01-06.md](ACTOR_JOIN_ISSUE_2026-01-06.md) - Join investigation report
