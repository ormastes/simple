# Actor Join Compilation Issue - 2026-01-06

## Summary

Attempted to implement compilation support for the `join` actor operation. The implementation is complete from a code perspective, but testing reveals that `join` returns `nil` instead of the expected `0` or `1`.

## Implementation Completed

1. **MIR Instruction**: `MirInst::ActorJoin { dest, actor }` added to `src/compiler/src/mir/inst_enum.rs`
2. **HIR Lowering**: Added handling in `src/compiler/src/hir/lower/expr/calls.rs` to recognize `join` and create `HirExprKind::BuiltinCall`
3. **MIR Lowering**: Added handling in `src/compiler/src/mir/lower/lowering_expr.rs` to convert `BuiltinCall{name: "join"}` to `MirInst::ActorJoin`
4. **Codegen**: Added in `src/compiler/src/codegen/instr.rs` to call `rt_actor_join` and tag the i64 result as RuntimeValue
5. **Effect System**: Updated `inst_effects.rs` and `inst_helpers.rs` to mark ActorJoin as blocking (Effect::Wait)
6. **Compilability**: Updated `compilability.rs` to mark only `reply` as non-compilable

## Issue Discovered

**Problem**: `join(actor)` returns `nil` instead of `1` (success) or `0` (failure).

**Evidence**:
- Test programs consistently show `join` returning `nil`
- No debug output from HIR lowering, MIR lowering, or codegen
- Runtime function `rt_actor_join` is never called (verified with debug prints)
- Actor `spawn` works correctly in the same programs

**Hypothesis**: The function containing `join` is being interpreted rather than compiled, despite `join` being marked as compilable. Possible causes:
1. Cached compilation artifacts not being refreshed
2. Another non-compilable construct in the test functions triggering interpreter fallback
3. Missing interpreter implementation of `join` causing `nil` return
4. Compilation path selection logic not recognizing the updated compilability status

## Next Steps

1. **Verify compilation path**: Add logging to determine if functions with `join` are being compiled or interpreted
2. **Check for interpreter fallback**: Investigate why rt_actor_join isn't being called
3. **Test in isolation**: Create a minimal test with ONLY spawn and join, no other builtins
4. **Clear all caches**: Delete all .smf files and force recompilation from scratch
5. **Consider adding interpreter implementation**: As a fallback, implement `join` in the interpreter similar to how `spawn` is handled

## Files Modified

- `src/compiler/src/value.rs` - Added BUILTIN_JOIN constant
- `src/compiler/src/hir/lower/expr/calls.rs` - HIR lowering for join
- `src/compiler/src/mir/inst_enum.rs` - Added ActorJoin variant
- `src/compiler/src/mir/lower/lowering_expr.rs` - MIR lowering for join
- `src/compiler/src/mir/inst_effects.rs` - Effect annotation
- `src/compiler/src/mir/inst_helpers.rs` - Helper methods (dest/uses)
- `src/compiler/src/codegen/instr.rs` - Codegen with i64→RuntimeValue tagging
- `src/compiler/src/compilability.rs` - Updated to enable join compilation
- `src/runtime/src/value/actors.rs` - Added debug output (should be removed)

## Test Cases

Test files created in `/tmp`:
- `test_join_raw.spl` - Basic join test with print
- `test_join_minimal.spl` - Minimal test without print
- `test_join_explicit.spl` - Explicit comparison test (exit code 44 = 300 % 256, confirms nil return)
- `test_join_new_file.spl` - Fresh test file

All tests show the same issue: join returns nil.
