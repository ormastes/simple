# Manual Memory Safety Plan (Simple)

## Summary
Strengthen manual memory safety rules in Simple by defaulting non-primitive values to unique ownership, requiring explicit mutability, and adding compiler/interpreter enforcement for aliasing, borrowing, and lifetime violations. The goal is to bring manual mode closer to Rust-style safety without losing Simple's GC and handle-pool flexibility.

## Goals
- Make manual memory usage safe by default for non-primitive values.
- Require explicit mutability and enforce exclusive access for mutation.
- Enforce aliasing and lifetime rules in compiler (static) with interpreter fallback (runtime checks) for cases the compiler cannot prove.
- Preserve existing pointer kinds: unique `&T`, shared `*T`, weak `-T`, handle `+T`.
- Avoid breaking GC mode or existing GC-based semantics.

## Non-Goals
- Replace GC as the default memory model for all use cases.
- Introduce a full Rust-like borrow checker in one step without staged rollout.
- Add cyclic GC for manual reference-counted `*T` values.

## Proposed Policy (Manual Mode)
- **Default ownership for non-primitive values:** a bare non-primitive type `T` in manual mode resolves to unique ownership (equivalent to `&T`) unless explicitly annotated with `*T`, `-T`, or `+T`.
- **Primitive values stay by-value:** numeric/boolean/char/etc. remain value types and do not default to `&T`.
- **Mutability must be explicit:** any mutation of a value requires explicit `mut` and an exclusive access path.
- **Mutation requires uniqueness or exclusive borrow:**
  - Mutating a unique owner (`&T`) is allowed only if it is declared `mut` and not aliased.
  - Mutating shared (`*T`) values is forbidden unless the value is obtained through an exclusive borrow (future `&mut` borrowing).

## Design and Architecture
- **Front-end ownership model:** pointer kinds are part of the type system; the compiler resolves bare non-primitive `T` to `&T` in manual mode and rejects implicit mixing (`&T` <-> `*T`) without explicit builtins.
- **Borrow/aliasing layer:** a dedicated analysis pass enforces exclusive mutable access or shared immutable access. This is separate from type inference to keep enforcement modular.
- **Lifetime/escape layer:** a MIR/CFG pass ensures borrows do not outlive owners or escape their scope.
- **Runtime debug checks:** optional cycle detection and borrow-violation checks remain in the runtime for cases the compiler cannot prove.
- **Domain separation:** GC allocations remain in the GC domain; manual allocations remain in manual/handle domains; explicit conversion is required between domains.

## Rust-Level Safety Conditions
- **Manual mode, strict:** Rust-like safety is achievable only when strict mode enforces aliasing and lifetime rules as errors.
- **Legacy mode:** not Rust-level safe by design (warnings only).
- **GC mode:** GC-managed objects are memory-safe, but manual/RC structures still need weak edges to avoid cycles (same as Rust Rc/Weak).

## Is Borrow Checking Required?
- **Yes for Rust-level guarantees:** without borrow checking (aliasing + lifetimes), manual mode cannot guarantee no use-after-free or invalid aliasing.
- **GC mode can omit borrow checking:** GC prevents UAF for GC-managed objects, but aliasing rules are still needed to prevent unsafe mutation patterns if manual pointers are involved.

## Implementation Design (Strict + Legacy)
- **Mode plumbing:** add `MemoryMode` (strict/legacy) to compiler pipeline options and interpreter context; expose `--memory-mode=strict|legacy` in CLI.
- **Legacy warnings:** implement memory-safety lints that mirror strict violations (mutability, aliasing, escaping borrows) and emit warnings in legacy mode.
- **Strict errors:** upgrade those lints to hard errors when strict mode is active.
- **Borrow/lifetime analysis:** introduce a borrow graph and region model in MIR/CFG; enforce non-escaping borrows, one-mut-or-many-immut rule, and forbid mutable access through shared pointers.
- **Runtime debug checks:** add cycle detection and borrow violation checks for debug builds, and surface as diagnostic errors.

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
- Introduce explicit borrow types in the type system (planned in `doc/design/memory.md`):
  - `&T_borrow` and `&mut T_borrow` for non-owning views.
- Add `mut` requirements to mutation operators and field assignments.
- Add type resolution rule for manual mode: `T` resolves to `&T` when `T` is non-primitive and not explicitly annotated.

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
- Phase 1: Implement ownership resolution for bare non-primitive `T` in manual mode.
- Phase 2: Enforce explicit `mut` and exclusive mutation rules.
- Phase 3: Add aliasing checks for borrows and shared pointers.
- Phase 4: Add lifetime/escape checks for borrows.
- Phase 5: Interpreter fallback checks for unproven cases.

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
