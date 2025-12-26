# Feature 100: Capture Buffer & VReg Remapping

**Importance:** 4/5  
**Difficulty:** 5/5  
**Status:** COMPLETED

## Goal
Encode live-ins for outlined bodies (actor/future/generator) into a `ctx` buffer at the call site, pass it through the runtime FFI, and remap vregs from `ctx` on outlined entry.

## Current State
- MIR computes live-ins per block and records `OutlinedBody { name, live_ins }`.
- Outlined functions clone the parent, prune to reachable blocks, force void returns, append a `ctx: i64` param.
- Codegen (Cranelift/JIT) packs live-ins into a runtime array (`rt_array_new/push`) and passes it to `rt_actor_spawn`, `rt_future_new`, `rt_generator_new`.
- Outlined bodies load captures from `ctx` via `rt_array_get` into vreg values before executing the body.
- Captures flow end-to-end in compiled actor/future/generator calls; runtime receives ctx and outlined bodies hydrate vregs from it.
- Tests (`cargo test interpreter_impl`) pass.
