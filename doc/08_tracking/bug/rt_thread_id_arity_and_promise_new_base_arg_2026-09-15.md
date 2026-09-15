# Runtime arity/constructor regressions: rt_thread_id and Promise.new executor (2026-09-15)

Two distinct src/runtime-side regressions found while fixing wave specs; both leave the
affected specs RED because the spec text is correct per sibling convention.

## 1. rt_thread_id expects 1 argument (handle)

- Specs: `test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl`,
  `actor_scheduler_ready_queue_spec.spl`.
- Observed: runtime error `rt_thread_id expects 1 argument (handle)` raised from inside
  the actor src path (specs contain no direct `rt_thread_id` call site).
- Unblock: align the src actor code with the current `rt_thread_id(handle)` extern
  signature (or restore a zero-arg variant), then both specs re-run unchanged.

## 2. Promise.new(executor) — "function expects argument for parameter 'base'"

- Spec: `test/01_unit/lib/nogc_async_mut/promise_spec.spl` (reduced 1/20 -> 13/20 on
  2026-09-15 by restoring the lost `enum/impl PromiseState` block mirrored from the
  passing `promise_intensive_spec.spl`; 7 remain RED).
- Observed: every `Promise.new(\resolve, reject: ...)` call fails at runtime with
  `function expects argument for parameter 'base', but none was provided`. The spec
  defines `static fn new(executor)` in `impl Promise<T>`; struct-literal construction
  `Promise { ... }` works, so it is static-constructor + lambda dispatch that breaks.
- Unblock: make `static fn new` callable as `Promise.new(executor)` again (the `base`
  parameter suggests dispatch hits a different `new` builtin), then the 7 remaining
  examples should pass unchanged.
