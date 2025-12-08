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

## Layout/ABI
- `common::gc` defines:
  - `GcAllocator` (alloc/collect)
  - `GcHandle<T>` opaque handle token
  - `GcRoot` for pinning (future)
- `common::manual` defines:
  - `ManualGc` + `Unique<T>` RAII owners with tracking (shared/weak/handle pointers still TODO)
  - Conversion helpers to be added alongside shared/weak/handle support
- Compiler lowers allocations:
  - Default: `GcAllocator::alloc_bytes`
  - Unique: stack or heap malloc/free
  - Shared/Weak: refcounted struct with vtable
  - Handle: runtime pool API

## Safety Rules (front-end)
- Pointer kinds are explicit in types; no implicit up/downcast.
- Assigning GC to manual requires `clone_*` builtin; type checker enforces.
- Destructor side-effects only in manual domain; GC domain is non-deterministic finalization.

## Testing
- GC logs via `--gc-log` to assert allocations/collections.
- Manual domain: leak-check tests for unique/shared lifetimes (once implemented).
