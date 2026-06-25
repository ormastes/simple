# Codegen Body Outlining Plan (Actors/Generators/Futures)

Goal: compiled actors/generators/futures should execute their `body_block` instead of the current no-op stub. We mirror a Rust-style closure ABI (`fn(ctx: *mut u8)`), but default to Erlang-style isolation by copying captures (no shared mutable state).

## Interpreter Baseline (already works)
- Actors run full bodies; message send/recv/join works (`interpreter.rs`, `interpreter_call.rs`).
- Generators use eager TLS collection of yields.
- Futures run the thunk and `await_result`.

## Current Codegen/Runtime State
- Codegen calls runtime FFI: `rt_actor_spawn/send/recv`, `rt_generator_new/yield/next`, `rt_future_new/await`.
- `body_block` is passed as a no-op stub; user code never runs in compiled mode.
- Runtime spawn accepts null body (no-op actor); generators are eager, futures are stubbed.

## Target ABI (Rust-style function pointer, Erlang-style isolation)
- Outlined body signature: `extern "C" fn(ctx: *const u8)` (single pointer arg).
- Captures are copied into a heap buffer (`RuntimeClosure`-like layout): first word reserved/unused, followed by captured `RuntimeValue`s (all copied, no shared mutation).
- Runtime FFI takes `(body_func: u64, ctx: RuntimeValue)` and calls `body_func(ctx_ptr as *const u8)`.
- Isolation choice: copy captures (Erlang-like isolation) to avoid shared mutable state; later we can allow move semantics when borrow rules are modeled.

## Implementation Steps
1) **MIR analysis**: for each `ActorSpawn/GeneratorCreate/FutureCreate`, compute live vregs at `body_block` entry. These become captures.
2) **Capture packaging**: emit code to allocate a capture buffer (reuse closure layout) and store captured `RuntimeValue`s in order.
3) **Outline `body_block`** into a new `MirFunction` with signature `fn(ctx: i64)`:
   - In the outlined function prologue, load captures from `ctx` buffer into vregs.
   - Jump to the original `body_block` instructions.
4) **Register outlined function**: add to `func_ids` so codegen can call `func_addr`.
5) **Codegen call sites**: replace stub pointer with `func_addr` of outlined body; pass capture buffer pointer as `ctx` to runtime FFI.
6) **Runtime FFI update**: change `rt_actor_spawn`, `rt_generator_new`, `rt_future_new` to accept `(body_func: u64, ctx: RuntimeValue)` and call `body_func(ctx_ptr as *const u8)` inside the spawned thread/generator/future.
7) **Generators**: interim—call outlined body once inside `rt_generator_new` to fill yields (still eager). Long-term—add state-machine transform so `Yield` suspends/resumes.
8) **Tests**: compiled actor roundtrip (spawn → send → recv), compiled generator yield/next, compiled future resolve/await.

## Complex Item: Live Capture Encoding
- Live vregs may include ints/floats/heap values. Store them as `RuntimeValue` in capture buffer.
- Buffer layout: `[u64 reserved_for_fnptr][capture0][capture1]...`.
- Prologue loads: for capture `i`, offset = 8 * (1 + i).
- This matches a simple Rust-style closure memory layout but keeps captures isolated (copy).

## Decision Notes (Rust vs Erlang)
- **ABI**: Rust-like `fn(ctx)` for simplicity and existing closure machinery.
- **Isolation**: Erlang-like copy of captures/messages to avoid shared mutation; later optimizations can introduce move/arc semantics.
- **Message payloads**: continue to pass raw `RuntimeValue` bits; future work can deep-copy heap values for stronger isolation.
