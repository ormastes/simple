# spl_thread_current_id: 0-arg source call vs 1-arg runtime backing

Date: 2026-09-16
Status: FIXED 2026-10-24 (worktree simple-rel100-port-20261024, uncommitted)

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

## Resolution 2026-09-16 section fixed 2026-10-24

Seed interpreter registration `insert_simple!("spl_thread_current_id", ...)`
was aliased to the 1-arg `concurrency::rt_thread_id`. Fix: new 0-arg
`concurrency::spl_thread_current_id` (stable per-OS-thread i64 from the
handle counter, thread-local) registered under the Simple name; the C runtime
ABI `rt_thread_id(handle)`/`spl_thread_current_id(void)` and the codegen spec
(`runtime_sffi.rs`, 0-arg) were already correct and are unchanged. Files:
`src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`. Seed rebuilt;
the Windows native-build probe (hello_world_client, cranelift) gets past the
former `rt_thread_id expects 1 argument (handle)` HIR-shard failure.
