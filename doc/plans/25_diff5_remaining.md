# Plan 25: Remaining Difficulty-5 Features

The following features in `doc/feature.md` have difficulty level **5** and are not yet marked complete. This plan tracks ownership and next actions to start each one.

| # | Feature | Notes / First Step |
|---|---------|--------------------|
| 13 | Type Inference | Finalize HM design in `doc/design/type_inference.md`, add HIR-typed nodes, and wire a unification engine (start with expressions only). |
| 14 | Generics/Type Parameters | Define generic instantiation rules and monomorphization pass; add HIR type args and trait bounds. |
| 24 | GC-Managed Memory (default T) | Land GC-backed allocator as default path and route codegen allocations through GC ABI (see `doc/design/memory.md`). |
| 29 | Borrowing (&T_borrow, &mut T_borrow) | Specify borrow checker model (align with `verification/manual_pointer_borrow`) and add borrow types to HIR/type checker. |
| 30 | Actors | Define `actor` syntax/AST, runtime scheduler contract, and MIR lowering to actor constructs. |
| 31 | Concurrency Primitives (spawn/send/receive) | Extend runtime queues/scheduler API and MIR instruction set; add codegen hooks using runtime FFI. |
| 32 | Async Effects | Add effect annotations to types, checker rules, and MIR lowering; gate async ops accordingly. |
| 33 | Stackless Coroutine Actors | Model actor bodies as state machines; reuse generator lowering to build dispatcher/resume paths. |
| 34 | Macros | Choose macro model (hygienic AST) and implement parser hooks + expansion phase before HIR typing. |
| 100 | Capture Buffer & VReg Remapping | Align outlined-body ctx layout and remap vregs post-liveness; update codegen to use deterministic offsets. |
| 101 | Generator State Machine Codegen | Complete MIR generator lowering/state metadata and ensure codegen dispatcher uses it (see `doc/plans/24_ui_dynamic_structure_and_hydration.md` for keyed ID discipline). |
| 126 | GPU Kernels (`#[gpu]` attribute for compute kernels) | Implement attribute parsing, SPIR-V lowering pipeline, and runtime kernel launch plumbing. |
| 510 | UI Dynamic Structure (render-time if/for, keyed lists) | Implement render control nodes, keyed diff, and structural PatchSet (see `doc/plans/24_ui_dynamic_structure_and_hydration.md`). |
| 511 | UI Structural PatchSet/Diff | Extend PatchSet with insert/remove/replace/move and integrate GUI/TUI renderers. |
| 512 | UI SSR + Hydration | Add server render output + hydration manifest; bind client wasm to existing DOM/tree. |

## Suggested sequencing
1. Core language semantics: 13/14/29 (type system foundation), 24 (GC default), 34 (macro entry point).  
2. Concurrency stack: 30/31/32/33 (actors/async) with shared runtime scheduler work.  
3. Codegen/runtime parity: 100/101 (outlined ctx and generators).  
4. UI platform: 510/511/512 (structural diff + SSR) after milestone 3 UI renderer.  
5. Platform expansion: 126 (GPU kernels) once core codegen/runtime is stable.
