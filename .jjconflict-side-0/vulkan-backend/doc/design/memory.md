# Memory Design: GC + Manual Cooperation

## Goals
- GC-managed default per Feature #24, but allow manual/unique/shared/weak/handle pointers without fighting the GC.
- Keep compiler/runtime contract narrow: compiler targets `common::gc::GcAllocator` and pointer-kind markers; runtime implements concrete policies.
- Avoid double-free/aliasing hazards when mixing manual and GC by separating ownership domains and requiring explicit conversions.

## Model
- **GC domain (default)**: values allocated via `GcAllocator`; opaque handles exposed to runtime; tracing via Abfall backend.
- **Manual domain**:
  - Unique (`&T`): RAII-owned; no aliasing; freed deterministically.
  - Shared (`*T`): refcounted; freed when count hits zero.
  - Weak (`-T`): non-owning; upgrade-or-nil semantics.
  - Handle (`+T`): pooled, managed by runtime (e.g., FDs, resources).
- **Interop**:
  - From GC -> manual: require explicit `clone_unique/clone_shared` builtins; compiler emits conversions via `common` ABI.
  - From manual -> GC: wrap in GC handle; manual source invalidated.
  - No implicit mixing; codegen chooses correct ABI call based on type.

## Borrow References (planned)
- Borrow types (`&T_borrow`, `&mut T_borrow`) are **non-owning views** over data in any domain (GC, unique, shared, handle pool slots). They never perform allocation or deallocation.
- Alias rules are purely static: multiple immutable borrows OR one mutable borrow of the same base at a time. Violations are compile-time errors; runtime only provides an escape hatch for unimplemented cases.
- Lifetimes are scoped to blocks/CFG regions; borrows to manual owners cannot outlive the owner move/drop, and borrows to GC values cannot outlive the lexical scope that created them.
- Handle pools expose borrowable views via `handle_get`/`handle_get_mut`; these return short-lived borrows tied to the pool slot and must not escape the call site.

## Layout/ABI
- `common::gc` defines:
  - `GcAllocator` (alloc/collect)
  - `GcHandle<T>` opaque handle token
  - `GcRoot` for pinning (future)
- `common::manual` defines:
  - `ManualGc` + `Unique<T>` RAII owners with tracking, `Shared<T>`/`WeakPtr<T>` for refcounted/weak, and `HandlePool`/`Handle<T>` for pool-managed handles.
  - Conversion helpers to be added alongside richer compiler lowering once pointer kinds are enforced in type checking.
- `runtime::memory` hosts:
  - `gc` (Abfall-backed tracing GC)
  - `no_gc` (GC-off profile: boxed allocations, `collect` is no-op) to support latency-critical builds; CLI/runtime can pick this via `--gc=off` or `SIMPLE_GC=off`.
- Compiler lowers allocations:
  - Default: `GcAllocator::alloc_bytes`
  - Unique: stack or heap malloc/free
  - Shared/Weak: refcounted struct with vtable
  - Handle: runtime pool API

## Current Implementation Snapshot
- Runtime exports `GcRuntime` (Abfall-backed) and `NoGcAllocator` under `runtime::memory`; both satisfy the `GcAllocator` contract from `common::gc`.
- Manual ownership helpers (`ManualGc`, `Unique`, `Shared`, `WeakPtr`, `HandlePool`, `Handle`) live in `common::manual` and are test-covered for leak/drop accounting; compiler does not yet enforce aliasing on top of them.
- Borrow references are specified in the language doc but not yet represented in compiler/types; no runtime enforcement exists beyond handle pool helpers returning short-lived views.

## Safety Rules (front-end)
- Pointer kinds are explicit in types; no implicit up/downcast.
- Assigning GC to manual requires `clone_*` builtin; type checker enforces.
- Destructor side-effects only in manual domain; GC domain is non-deterministic finalization.

## Incremental Plan (borrowing + memory)
- Step 1: Add borrow reference variants to the AST and `type` crate; thread through parser/formatter without enforcement.  
- Step 2: Enrich type inference with borrow qualifiers and forbid invalid coercions (e.g., `&mut` to `&mut` of a different base).  
- Step 3: Introduce a lightweight MIR/CFG pass for local aliasing (one `&mut` or many `&`), covering GC and manual owners equally.  
- Step 4: Add block-scoped region tracking to reject escaping borrows and storing borrows into longer-lived fields unless proven safe.  
- Step 5: Extend checks to captures/actors and handle pools, keeping runtime free of borrow-state while offering a gated runtime-checked fallback for unsupported patterns.

## Testing
- GC logs via `--gc-log` to assert allocations/collections.
- Manual domain: leak-check tests for unique/shared lifetimes (once implemented).
