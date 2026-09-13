# Bug: ds_utils T? return inconsistently wraps in Option::Some

## Closed 2026-09-13 — `T?` returns no longer wrap in `Option::Some`
- **measured** (Windows Rust seed v1.0.0-rc.1, `bin/simple run`): impl methods `fn peek() -> i64?`, `me pop() -> i64?` and a free `fn free_peek(...) -> i64?` all printed bare values (`peek=20`, `pop=20`, `free=7`) and bare `nil` on empty (`empty_peek=nil`, `free_empty=nil`) — no `Option::Some(...)` / `Option::None` leakage in either the impl-method or free-function arm.
- **measured**: same result under both `SIMPLE_EXECUTION_MODE=interpret` and `=jit`.
- **inferred**: the spec was not re-run; `bin/simple test` is non-functional on this Windows host (trivial spec reports a false `outer-bound-timeout`).

**Date:** 2026-06-26
**Spec:** `test/01_unit/lib/common/ds_utils_stack_queue_spec.spl`
**Source:** `src/lib/tooling/ds_utils.spl`

## Symptoms (18 failures)

Two failure patterns in `bin/simple test`:

### Pattern 1: T? methods wrap return values inconsistently (10 failures)
Same `fn peek() -> T?` method on `Stack` passes in one test but fails in another:
- `Stack peek()` in "peeks at top element" → returns bare `20` (passes `to_equal(20)`)
- `Stack peek()` in "creates stack from list" → returns `Option::Some(30)` (fails `to_equal(30)`)

Other affected methods: `me pop() -> T?`, `me dequeue() -> T?`, `me pop_front() -> T?`,
`me pop_back() -> T?`, `fn peek_front() -> T?`, `fn peek_back() -> T?`.

Error form: `expected Option::Some(N) to equal N`

### Pattern 2: `to_be_nil()` does not match `Option::None` (8 failures)
When a T? method returns nil on empty collection, it returns `Option::None`. The `to_be_nil()`
matcher does not match `Option::None`.

Error form: `expected Option::None to be nil`

Affected: empty-collection edge cases for pop, peek, dequeue, pop_front, pop_back,
peek_front, peek_back on all three types.

## Root cause

Interpreter inconsistency: the same `-> T?` method on an `impl` block sometimes wraps
its return value in `Option::Some` and sometimes returns the bare value. The wrapping
appears context-dependent (order of test execution or internal interpreter state).

The free-function wrapping bug is already known and worked around in `stack_get` / `queue_get`
via `-> any` return type (see `ponytail:` comment at line 183 of ds_utils.spl and bug
`free_fn_optional_wrap_2026-06-26`). The impl-method case was believed unaffected, but
this spec demonstrates it is also intermittently affected.

Additionally, `to_be_nil()` does not handle `Option::None` (separate known matcher bug).

## Impact

18 of ~50 tests in `ds_utils_stack_queue_spec.spl` fail. Cannot be fixed by spec changes
alone because the same API call yields inconsistent results in different test contexts.

## Fix needed

1. Interpreter: ensure `-> T?` impl-method returns are not wrapped in `Option::Some`.
2. Matcher: `to_be_nil()` should treat `Option::None` as nil (see also the nil-matcher bug).
