# Manual Memory Safety Plan (Simple)

## Summary
Strengthen manual memory safety rules in Simple by defaulting to unique owning handles (`&T`, implicit), using explicit shared handles (`*T`), forbidding user-visible borrows/lifetimes, and adding compiler-inserted lifecycle operations (retain/release/drop) with debug tracing. The goal is a safe, predictable manual mode without non-owning references or lifetime syntax.

## Goals
- Make manual memory usage safe by default via implicit unique ownership (`&T`) and explicit shared ownership (`*T`).
- Remove user-visible borrow/lifetime syntax from the safe subset; rely on ownership lifetimes only.
- Enforce mutation rules: shared handles are read-only; mutation requires unique ownership or consume-and-return COW.
- Insert compiler-managed lifecycle ops (move/drop/rc_inc/rc_dec) with debug visibility.
- Avoid breaking GC mode or existing GC-based semantics.

## Non-Goals
- Replace GC as the default memory model for all use cases.
- Introduce borrow/lifetime syntax or borrow regions in the safe subset.
- Add cyclic GC for manual reference-counted `*T` values.

## Proposed Policy (Manual Mode)
## Proposed Policy (Manual Mode)
- **Default ownership:** bare `T` in expression/local contexts resolves to `&T` (unique owning handle) unless explicitly `*T`.
- **Primitive values stay by-value:** numeric/boolean/char/etc. remain value types.
- **No user-visible borrows:** no `&T_borrow`/`&mut T_borrow` in the safe subset.
- **Shared is read-only:** `*T` is copyable and refcounted; mutation is forbidden directly.
- **Mutation requires unique ownership:** methods that mutate require `&T` receiver (implicit `T`).
- **No `var *T`:** shared owners cannot be mutated in place; updates use consume-and-return patterns.

## Design and Architecture
- **Front-end ownership model:** pointer kinds are part of the type system; the compiler resolves bare `T` to `&T` in manual mode and rejects implicit mixing (`&T` <-> `*T`) without explicit builtins.
- **Lifecycle lowering:** compiler inserts explicit handle ops (move/drop/rc_inc/rc_dec) and schedules them on scope exit (or NLL-style last-use).
- **Mutation gating:** mutating methods require unique receiver; shared receivers expose only read methods and consume-return updates.
- **Runtime debug checks:** optional cycle detection and lifecycle tracing for debug builds.
- **Domain separation:** GC allocations remain in GC domain; manual allocations remain in manual/handle domains; explicit conversion required between domains.

## Rust-Level Safety Conditions
- **Manual mode, strict:** Rust-like safety is achievable when strict mode enforces ownership + refcount rules and forbids shared mutation.
- **Legacy mode:** not Rust-level safe by design (warnings only).
- **GC mode:** GC-managed objects are memory-safe, but manual/RC structures still need weak edges to avoid cycles (same as Rust Rc/Weak).

## Is Borrow Checking Required?
- **No, if the safe subset forbids non-owning references:** memory safety comes from owning handles only.
- **Yes, if non-owning references are reintroduced later:** borrow/lifetime rules would be required then.

## Implementation Design (Strict + Legacy)
- **Mode plumbing:** add `MemoryMode` (strict/legacy) to compiler pipeline options and interpreter context; expose `--memory-mode=strict|legacy` in CLI.
- **Legacy warnings:** implement memory-safety lints that mirror strict violations (shared mutation, implicit copies of unique, COW misuse) and emit warnings in legacy mode.
- **Strict errors:** upgrade those lints to hard errors when strict mode is active.
- **Lifecycle lowering:** insert `u_move/u_drop` and `rc_inc/rc_dec` ops in MIR/CFG; enforce exactly-once drop/decrement.
- **Runtime debug checks:** add cycle detection and lifecycle tracing for debug builds, surfaced as diagnostic errors.

## Core Semantics (Implicit & and Explicit *)
### &T — unique owner (default, implicit)
- Owns exactly one allocation of `T`.
- Move-only; copies are errors.
- Dropping frees the allocation and runs `drop(T)`.
- **Defaulting rule:** a type written as `T` in expression/local contexts is interpreted as `&T` unless explicitly `*T`.

### *T — shared owner (refcount)
- Copyable; copies increment refcount.
- Dropping decrements refcount; frees allocation at zero.
- Read-only in safe code; mutation is forbidden directly.
- `var *T` is forbidden.

## Implicit Lifecycle Handle Model (Compiler-Inserted)
### Handle kinds (internal)
- `HUnique(T)` for `&T`
- `HShared(T)` for `*T`

### Inserted operations (internal)
- **Unique:** `u_move`, `u_drop`
- **Shared:** `rc_inc`, `rc_dec`, `rc_clone`
- **Scope-based lifetime:** compiler schedules drops/decrements at end of scope (or last-use).

### Debug tracing
- `--debug-lifecycle`: show inferred drop points for `&`
- `--debug-rc`: show `rc_inc`/`rc_dec` insertion sites
- `--debug-cow`: show clone-on-write operations

Example format:
```
RC_INC  f.spl:12:9  *Vec[Int]  reason=copy to x2
DROP    f.spl:19:1  &Foo       reason=end_of_scope
```

## Mutation and COW (Consume-and-Return)
- **Mutating methods require unique receiver** (`&T`, implicit `T`).
- **Shared updates use COW** (consume `*T`, return `*T`).
- Primitives:
  - `into_unique[T: Clone](x: *T) -> T` (COW: reuse if rc==1, else clone)
  - `share[T](x: T) -> *T`
- Standard pattern:
  - `method mut(self: *T, f: fn(T)->Void) -> *T` desugars to `into_unique -> f -> share`.

## Surface Restrictions (Required for Soundness)
- **No interior views in v1:** container getters return values or cloned owners; no view into internal buffers.
- **No shared mutation:** `*T` does not expose mutating methods; updates return new `*T`.

## Affected Components (What to Update)
- **Parser/AST:** add explicit borrow types `&T_borrow` and `&mut T_borrow` and ensure they round-trip through formatter.
- **Type system (`type` crate):** encode borrow kinds, mutability, and pointer-kind defaults; update substitution and contains-var for new types.
- **Type checker:** enforce default-unique resolution in manual mode, explicit mutability, and forbid implicit pointer-kind conversions.
- **MIR/CFG passes:** add alias/borrow checks and lifetime/escape checks.
- **Interpreter/runtime:** add debug-mode borrow/cycle checks; plumb error diagnostics with source spans.
- **Stdlib annotations:** mark APIs that return borrows (e.g., handle pool access) and ensure they cannot escape.
- **Specs/tests:** update `tests/specs/memory_spec.spl` and regenerate `doc/spec/generated/memory.md` once the rules are enforced.

## Shared Logic (Compiler + Interpreter)
- **Borrow graph model:** build a shared representation of borrows/owners in `common` so both compiler and interpreter can reuse logic and error formatting.
- **Pointer-kind resolution:** implement a single helper for default-unique resolution and pointer-kind compatibility checks.
- **Diagnostics:** share violation codes/messages (e.g., `E_MEM_ALIAS`, `E_MEM_ESCAPE`, `E_MEM_CYCLE`) between compiler and interpreter.

## Syntax/Type System Changes
### Syntax/Type System Changes
- Keep pointer kinds `&` and `*` only; no `owned` keyword.
- Remove/disable borrow/lifetime syntax in the safe subset.
- Add type normalization rule: bare `T` resolves to `&T` in manual mode.
- Add `mut` requirements to mutation operators and field assignments.

## Compiler Enforcement (Static)
1. **Ownership resolution pass**
   - Resolve bare non-primitive `T` to `&T` in manual mode.
   - Reject implicit conversion between `&T` and `*T` without explicit builtins (existing rule).

2. **Alias/borrow checker (phase 1)**
   - Enforce at most one mutable access or multiple immutable accesses at a time.
   - Reject writes through shared `*T` or weak `-T` unless converted to an exclusive borrow.

3. **Lifetime/escape analysis (phase 2)**
   - Forbid borrows that outlive their owners.
   - Forbid storing borrows into longer-lived fields unless proven safe.

4. **Actor/capture checks (phase 3)**
   - Prevent borrows crossing actor boundaries or escaping async tasks without explicit ownership transfer.

## Interpreter/Runtime Enforcement (Fallback)
- Add optional runtime checks when the compiler cannot prove exclusivity:
  - Detect double mutable borrows.
  - Detect use-after-move for `&T`.
  - Detect invalid handle borrows (`+T`) escaping their scope.
- Gate runtime checks behind a debug flag and error on violation.

## Debug Cycle Detection (GC and no_gc)
- **GC mode:** add a debug-only verification pass that walks the GC heap after collection to flag strongly connected components that remain reachable only through refcounted/manual edges (indicates a cycle retained by RC/handles).
- **no_gc/manual RC:** add a debug-only heap graph scan for `*T` objects and fail if a refcount cycle is detected without a `-T` weak edge.
- **Policy:** debug builds treat detected cycles as errors; release builds do not scan.

## Circular References
- Manual `*T` remains refcounted and will not collect cycles.
- Encourage design patterns using `-T` weak links for cyclic graphs.
- Document that GC mode is the recommended choice for cyclic object graphs.

## Migration Plan
- Phase 0: Document new rules in `doc/spec/memory.md` and `tests/specs/memory_spec.spl`.
- Phase 1: Implement implicit `&` normalization for bare `T` in manual mode.
- Phase 2: Implement handle lowering (`u_move/u_drop/rc_inc/rc_dec`) and drop scheduling.
- Phase 3: Enforce move-only `&T` and forbid `var *T` + shared mutation.
- Phase 4: Add COW primitives (`into_unique`, `share`) and stdlib `mut()` pattern.
- Phase 5: Add debug lifecycle/rc/cow tracing and cycle detection.

## Dual-Mode Compilation (Strict + Legacy)
- **Mode names:** `--memory-mode=strict` and `--memory-mode=legacy` (default: legacy during migration).
- **Strict mode:** enforces all new manual memory safety rules.
- **Legacy mode:** allows existing behavior but emits warnings for violations that would be errors in strict mode.
- **Warnings policy:** legacy warnings are targeted and actionable (include suggested fixes); after migration, legacy warnings can be removed and legacy mode deprecated.

## Refactor Scope (NoGC Libraries + Apps)
- **Stdlib no_gc variants:** `simple/std_lib/src/core_nogc`, `simple/std_lib/src/core_nogc_immut`, `simple/std_lib/src/host/async_nogc_mut`, `simple/std_lib/src/host/sync_nogc_mut`, `simple/std_lib/src/gpu/host/async_nogc_mut`, `simple/std_lib/src/bare`, `simple/std_lib/src/gpu/kernel`.
- **Apps/examples/tests:** all `.spl` under `example/`, `test/`, `tests/`, and `simple/app/` that target no_gc or manual ownership patterns.
- **Refactor order:** core_nogc → host async/sync nogc → gpu/bare → apps/tests.

## Refactor Rules (Legacy → Strict)
- Replace implicit shared/mutable patterns with explicit `&T` or borrow where required.
- Add explicit `mut` on owners that are mutated; add borrow-only views where mutation is not needed.
- Replace RC cycles with `-T` weak edges in no_gc/manual code.
- Add explicit conversions for GC/manual boundaries (no implicit conversions).

## Compiler Integration Points
- **CLI/driver:** add `--memory-mode` flag; propagate into parser/type checker/MIR passes.
- **Type checker:** select strict vs legacy rule sets; emit warnings in legacy for strict violations.
- **Diagnostics:** add warning codes (e.g., `W_MEM_MUT`, `W_MEM_ALIAS`, `W_MEM_ESCAPE`, `W_MEM_CYCLE`) and map to strict errors.
- **Testing:** add paired tests that ensure strict errors and legacy warnings for the same code paths.

## Tests
- Add positive and negative tests in `tests/specs/memory_spec.spl`:
  - Bare non-primitive defaults to unique in manual mode.
  - Mutation requires `mut` and exclusive access.
  - Illegal mutation through shared `*T` rejected.
  - Borrow does not escape owner scope.
  - Weak pointer cycles require explicit `-T`.

## Risks
- Backwards compatibility for code relying on GC-default `T`.
- Increased compile-time cost due to borrow and lifetime analysis.
- False positives from conservative lifetime checks in early phases.

## Open Questions
- Exact definition of "primitive" for default-unique resolution.
- How manual mode is selected (profile/attributes) and how mixed modes are handled.
- Whether `mut` implies unique ownership or is orthogonal to ownership.

## Deliverables
- Spec updates: `doc/spec/memory.md` and `tests/specs/memory_spec.spl`.
- Compiler passes for ownership resolution and borrow checking.
- Interpreter debug checks for violations.
- Migration notes in `doc/spec/MIGRATION_STATUS.md` if needed.
