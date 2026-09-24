# spl_thread_current_id: 0-arg source call vs 1-arg runtime backing

Date: 2026-09-16
Status: OPEN

## Observed

`actor_scheduler_ready_queue_spec.spl` fails with
`function rt_thread_id expects 1 argument but is called with 0`:
`spl_thread_current_id()` is declared/called with zero arguments, but its
runtime backing `concurrency::rt_thread_id` takes one argument
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2274`,
`src/compiler_rust/.../concurrency.rs:548`).

## Impact

Anything calling `spl_thread_current_id()` in the interpreter fails; the actor
scheduler ready-queue spec cannot execute.

## Expectation

Either the extern mapping supplies the implicit thread handle, or the Simple
wrapper passes the argument.

## Unblock condition

Fix the extern arity mapping (seed-side Rust), rebuild the seed, re-run
`test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl`.
