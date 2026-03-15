# Bug: `while` loops don't execute inside `it` blocks

**Severity:** P1
**Status:** Open (partially investigated)
**Reported:** 2026-03-15

## Reproduction

```simple
# Top level — WORKS
var x = 0
while x < 3:
    x = x + 1
# x == 3

# Inside it block — BROKEN
describe "test":
    it "while loop":
        var y = 0
        while y < 3:
            y = y + 1
        expect(y).to_equal(3)  # FAILS: y is still 0
```

`for` loops and `for ... in range` work correctly inside `it` blocks. Only `while` is broken.

## Investigation

1. `bin/simple run` dispatches `describe`/`it` as regular function calls
2. The BDD handler in `interpreter_call/bdd.rs` line 599 calls `exec_block_value(block, ...)`
3. Debug prints added to `bdd.rs` and `lambda.rs` were **never reached** — `bin/simple run` uses a different code path than expected
4. The `it` block body execution likely goes through the main interpreter's `exec_node` dispatch in `node_exec.rs` line 223, where `Node::While` is handled by `exec_while` from `interpreter_control.rs`
5. The main `exec_while` works (proven by top-level while loops working)
6. The issue is specific to the **scope/environment** in which `it` block bodies execute

## Partial Fixes Applied

- Added `Node::While` and `Node::Loop` handlers to `exec_block_closure_mut` in `block_execution.rs`
- Changed `exec_lambda` in `lambda.rs` to use `exec_block_closure_mut` (mutable env) instead of `exec_block_closure`
- Changed `exec_block_value` in `bdd.rs` to use `exec_block_closure_mut`
- Made `exec_block_closure_mut` `pub(crate)`

These fixes did NOT resolve the issue because the `it` block body doesn't go through these code paths when using `bin/simple run`.

## Workaround

Use `for` loops instead of `while` inside `it` blocks:

```simple
# Instead of:
var i = 0
while i < 5:
    # do something
    i = i + 1

# Use:
for i in 0..5:
    # do something
```

## Files Modified

- `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` — Added While/Loop handlers, made pub(crate)
- `src/compiler_rust/compiler/src/interpreter_call/core/lambda.rs` — Use mutable env for DoBlock
- `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` — Use mutable closure execution
- `src/compiler_rust/compiler/src/codegen/mir_interpreter.rs` — MIR collection size tracking (unrelated fix)

## Next Steps

1. Add debug tracing to the ACTUAL code path used by `bin/simple run` for `it` block dispatch
2. Find where `while` loop bodies are skipped in that specific execution context
3. The fix is likely a one-line change once the correct code path is identified
