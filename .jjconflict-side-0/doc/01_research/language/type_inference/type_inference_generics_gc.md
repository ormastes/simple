# Research Notes — Features #13 (Type Inference), #14 (Generics), #24 (GC-Managed Default)

## References
- `plans/02_parser_implementation.md` (types/generics)
- `plans/05_ahead_of_time_compile.md` (type variables mention)
- `plans/07_basic_types.md` (GC integration hooks)

## Type Inference (Feature #13)
- Target: Hindley–Milner-style inference for let-bindings and function params/returns.
- Minimal viable: local inference (let-binding RHS, function bodies) with explicit annotations optional; propagate constraints to unify AST types.
- Components:
  - Parser: type annotations optional on `let`, params, returns.
  - Type system: type variables, unification, occurs check, constraint graph.
  - Compiler: insert type-mono substitutions into MIR/codegen.
- Pitfalls: inference across method calls (requires trait/impl resolution), recursion (generalization), higher-rank types (avoid initially).

## Generics (Feature #14)
- Target: parametric functions/types with monomorphization.
- Components:
  - Parser: parse `<T, U>` on functions/types; generic args on call sites/type uses.
  - Type system: instantiate generics with fresh type variables; check constraints.
  - Monomorphization: clone IR per concrete instantiation (per call site or per specializable set).
  - ABI: mangle names with type params; loader unchanged.
- Pitfalls: generic methods on classes, trait bounds (future), code bloat; need instantiation cache.

## GC-Managed Default (Feature #24)
- Target: default allocations are GC-managed; pointer kinds (unique/shared/weak/handle) are explicit opts.
- Components:
  - `runtime/gc/`: Abfall-backed runtime already exists (`GcRuntime`).
  - `common`: define opaque GC handle types/traits (GcHandle/GcRoot/GcAllocator) for compiler/runtime contract.
  - Compiler: emit GC allocations for aggregates/strings by default; only unique/shared pointers opt-out.
  - Driver: GC logging flag already exists; expose toggles for GC options via env/args.
- Pitfalls: FFI boundaries, cycles in class instances, drop semantics for unique/shared not yet modeled.

## Rollout strategy (shared)
- Start with parser/type-system scaffolding (type vars, generics syntax).
- Add inference/unification on a small IR (HIR) before touching codegen.
- Introduce GC handle abstractions in `common`, adapt runtime wrapper, then teach codegen to allocate via GC (stubbed until codegen matures).
