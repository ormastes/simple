# Plan 20: Codegen Body Outlining for Actors/Generators/Futures

## Goal
Replace the current no-op stub for `body_block` in ActorSpawn/GeneratorCreate/FutureCreate with real compiled bodies. Align with Rust-style `fn(ctx)` ABI while keeping Erlang-style isolation (copy captures into ctx).

## Current State
- Runtime FFI accepts `(body_func, ctx)` and calls `body_func(ctx)` for actors/generators/futures.
- Codegen passes a no-op stub and `nil` ctx (no user body runs when compiled).
- Interpreter executes full bodies for actors/generators/futures.

## Target Design (Rust ABI, Erlang isolation)
- Outlined function signature: `extern "C" fn(ctx: *const u8)`.
- Captures: copy live `RuntimeValue`s into a heap buffer (closure-like layout) to avoid shared mutation.
- Runtime calls `body_func(ctx_ptr)` inside actor thread/generator/future runner.

## Steps
1. **Live capture analysis**  
   - Compute live vregs at `body_block` entry for ActorSpawn/GeneratorCreate/FutureCreate.
   - Order captures deterministically (e.g., sorted vreg index).

2. **Capture packaging**  
   - Emit code to allocate a capture buffer (reuse closure layout or simple array of `RuntimeValue`).
   - Store captured values before calling runtime creation.

3. **Outline body_block**  
   - Create a new `MirFunction` per `body_block` with signature `fn(ctx: i64)`.
   - Prologue loads captures from `ctx` into vregs, then jumps to original body instructions/terminator.
   - Register the new function in `func_ids`.

4. **Codegen plumbing**  
   - Replace stub pointer with `func_addr` of the outlined function.
   - Pass capture buffer pointer as `ctx` to `rt_actor_spawn`/`rt_generator_new`/`rt_future_new`.

5. **Runtime consistency**  
   - Ensure runtime uses `(body_func, ctx)` everywhere and copies ctx pointer faithfully into the call.

6. **Generators (interim)**  
   - Call outlined generator body once in `rt_generator_new` to fill yields (still eager).  
   - Future work: MIR state-machine transform so `Yield` suspends/resumes.

7. **Tests**  
   - Compiled actor roundtrip: spawn → send → recv (body echoes).  
   - Compiled generator yield/next: body yields constants.  
   - Compiled future resolve/await: body sets state/result.

## Risks/Decisions
- Capture copy vs move: start with copy (Erlang isolation) to avoid shared mutation; optimize later.
- Capture layout: reuse existing closure layout for consistency with other codegen paths.
- Ordering: deterministic capture order is required for stable offsets.

## Done Criteria
- No stub use: `func_block_addr` returns outlined functions.
- Runtime receives non-null body pointers for actor/generator/future from codegen path.
- Tests above pass in compiled mode.
