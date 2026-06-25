# Interpreter vs Codegen: Concurrency/Generators/Futures

## Overview
The interpreter already executes actors, generators, and futures end-to-end. Codegen now calls runtime FFI for spawn/send/recv and yield/next but still uses a no-op stub for `body_block` (actors/generators/futures don’t run user bodies when compiled). This note captures the current gap and what’s needed.

## Interpreter Implementation (works today)
- **Actors**: `src/compiler/src/interpreter.rs` (`ACTOR_SPAWNER`, `ACTOR_INBOX`, `ACTOR_OUTBOX`) and `interpreter_call.rs` (`send`, `recv`, `reply`, `join`) run real actor bodies and message passing with timeout.
- **Generators**: `interpreter.rs` handles `Expr::Yield` with TLS `GENERATOR_YIELDS` and builds `GeneratorValue` eagerly.
- **Futures**: `interpreter_call.rs` builds `FutureValue` (runs a thunk on spawn, `await_result`).

## Codegen/Runtime Status (after recent wiring)
- Runtime FFI exists: `rt_actor_spawn/send/recv`, `rt_generator_new/yield/next`, `rt_future_new/await`.
- Codegen declares these and replaces traps, but `body_block` is passed a no-op stub (no user code runs in compiled mode).
- Generator runtime is eager (one-shot collect) and ignores compiled generator bodies.

## What the Compiler Still Needs
1) **Outline `body_block`** into a standalone function with a stable signature (e.g., `fn(ctx: i64)`), register it, and use `func_addr` instead of the stub.  
2) **Capture plumbing**: package live vregs into a closure/ctx value and pass it to the outlined body; load captures inside the body.  
3) **Runtime FFI update**: accept a ctx pointer for actor/future/generator bodies and call `body_ptr(ctx)` inside the spawned thread/generator/future runner.  
4) **Generator semantics**: replace eager TLS collection with either (a) call the outlined body once to populate yields, or (b) proper state-machine transformation so `Yield` suspends/resumes.  
5) **Tests**: compiled actor roundtrip (spawn→send→recv), compiled generator yield/next, compiled future resolve/await.

## Complex Item: Body Outlining + Captures (design direction)
- **Signature**: use `extern "C" fn(ctx: i64)` for outlined bodies to allow a closure/ctx pointer.  
- **Capture layout**: reuse the closure layout already used in codegen (first word fn ptr, following words captured `RuntimeValue`s); or a simple packed array.  
- **Call path**: spawn/create allocates the capture object, stores live vregs, and passes its pointer as `ctx` to the runtime. The runtime calls `body_ptr(ctx)` inside the actor thread/generator/future.  
- **Isolation choice**: prefer Erlang-like isolation by copying `RuntimeValue`s into the capture (no shared mutable state); Rust-like move semantics can follow once borrow rules exist in codegen.
