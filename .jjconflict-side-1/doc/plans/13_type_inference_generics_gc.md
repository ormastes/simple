# Plan: Features #13 (Type Inference), #14 (Generics), #24 (GC-Managed Default)

## Goals
- Add Hindley–Milner-style local type inference for let-bindings/functions (Feature #13).
- Support generic functions/types with monomorphization (Feature #14).
- Establish GC-managed default allocations via a stable ABI (Feature #24).

## Scope & Constraints
- Keep parser changes minimal: optional type annotations on lets/params/returns; parse generic params/args.
- Implement inference/unification in a dedicated type checker (HIR stage) before codegen.
- GC: expose opaque GC handle/allocator traits in `common`; codegen uses them once real backend exists.
- Avoid runtime AOP; use `tracing` instrumentation for debug builds only.

## Work Breakdown
1) Parser / AST
   - Allow generic params on `fn`/types; generic args on calls/type uses.
   - Optional type annotations already supported; ensure they surface to HIR.
2) Type System (new module)
   - Define `TypeVar`, `Type`, `Scheme`, `Env`, `Constraint`.
   - Implement unification + occurs check; generalize at let-binding; instantiate at use sites.
   - Add constraint generation for expressions, function defs, calls, methods.
3) Monomorphization (codegen prep)
   - Maintain instantiation cache keyed by concrete type args; clone IR per instantiation.
   - Mangle symbol names with type args; plumb into SMF symbol table.
4) GC-managed default
   - In `common`: add `GcHandle<T>`, `GcRoot`, `GcAllocator` trait.
   - In `runtime`: adapt `GcRuntime` to implement allocator trait.
   - In compiler codegen: route allocations through allocator API; default heap allocations are GC.
   - CLI: expose GC options flag/env; re-use existing `--gc-log`.
5) Testing
   - Unit: unification, inference of let/params, generic instantiation cache.
   - Integration/system: driver tests for inferred types, generic functions, GC allocation path (log markers).

## Acceptance Checklist
- Inference succeeds on unannotated lets/functions; type errors reported with spans.
- Generic functions/types parse and monomorphize; symbol names mangle type args.
- Default allocations use GC allocator hook; GC logs show collections under load.
- New tests in place (type inference, generics, GC logging path).
