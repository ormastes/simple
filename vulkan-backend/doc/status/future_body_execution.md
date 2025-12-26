# Feature 102: Future Body Execution (Compiled)

**Importance:** 4/5
**Difficulty:** 4/5
**Status:** COMPLETE

## Goal
Run compiled future bodies (not stubs), including ctx capture, and allow awaiting compiled futures.

## Current State
- Outlined bodies are generated and passed to `rt_future_new` with captured ctx.
- Captures are packed into a runtime array and reloaded in outlined entry.
- Runtime `rt_future_new` eagerly executes body with `fn(ctx) -> RuntimeValue` signature and stores result.
- `rt_future_await` returns the stored result (ready futures return value immediately).
- Codegen updated to make future outlined bodies return I64 (like generators).

## Completed System Tests (runner_tests.rs)
- `runner_future_basic` - create and await simple future
- `runner_future_with_computation` - future with function call
- `runner_future_multiple` - multiple independent futures
- `runner_await_non_future` - await on non-future value
- `runner_future_function_call` - future wrapping function call
- `runner_async_fn_basic` - async fn returning value
- `runner_async_can_call_async` - async fn calling other async
- `parity_future_basic` - interpreter/codegen parity test
- `parity_future_with_function` - interpreter/codegen parity test

## Gaps (future work)
- ~~Future body execution is still eager and returns NIL; no await/resume semantics.~~ **DONE**
- ~~No compiled tests proving captured ctx inside future bodies.~~ **DONE**
- No integration with an executor/scheduler (current execution is synchronous/eager).

## Next Steps
1) ~~Add compiled test that asserts a future body runs and sees captured values.~~ **DONE**
2) ~~Extend runtime to store result and gate `rt_future_await` on readiness.~~ **DONE**
3) ~~Wire await to resume compiled futures rather than returning NIL.~~ **DONE**
4) (Future) Add true async executor for concurrent/non-blocking execution. 
