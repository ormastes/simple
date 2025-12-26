# Plan 21: Generator State Machine Codegen (Yield Implementation)

## Goal
Implement compiled `yield`/`next` by transforming generator bodies into a stackless state machine (Rust async-style), eliminating the current eager collection + stub body.

## Current State
- Runtime FFI: `rt_generator_new(body_func, ctx)`, `rt_generator_yield(value)`, `rt_generator_next(gen)`.
- Codegen: calls runtime but still uses a stubbed body pointer; generator runtime collects yields eagerly.
- Interpreter: correct eager generator behavior.

## Target Design
- MIR transformation: convert generator body into a state machine function: `fn(ctx: *const u8, state_ptr: *mut GenState) -> ()`.
- State struct: `{ state: u32, yielded: RuntimeValue, saved locals... }`.
- Yield points become state transitions: store `yielded`, update `state`, return.
- `rt_generator_next` calls state machine to advance one step; returns `yielded` or `nil` if complete.

## Steps
1. **Yield analysis**: find yield points, compute live locals at each yield.
2. **State layout**: build a struct with discriminant + per-yield saved locals + last yielded value.
3. **Transform MIR**: replace generator body with a dispatcher over `state`, restore locals, run until next yield/return.
4. **Codegen**: emit state machine function, pass pointers to runtime via `rt_generator_new`.
5. **Runtime**: update `rt_generator_new/next` to allocate state buffer, call state machine, and set `yielded`/`state`.
6. **Tests**: compiled generator with multiple yields; looped `next` over range; exhaustion returns `nil`.

## Decisions
- Suspension granularity: yield-only (no await) in this phase.
- Capture model: copy captures into ctx buffer (Erlang isolation), restore into state as needed.
- Ordering: deterministic index for saved locals per yield.
