# JIT-compile failure anywhere in the whole-program closure → interpreter fallback loses a struct's 2nd+ static method registration

**Date:** 2026-07-20
**Scope:** `bin/release/x86_64-unknown-linux-gnu/simple` (self-hosted binary) JIT-to-interpreter fallback path (compiler internals — needs a rebuild to verify current source, not a `.spl` source edit)
**Severity:** medium — silently drops real static methods; no compile error, just a runtime "unknown static method" that looks like a source bug
**Related:** NOT the `gc_sync_mut` shim/tier-collision issue (that hypothesis was tested and disproven for this symptom — see
`doc/08_tracking/bug/gc_sync_mut_shim_fallback_struct_collision_2026-07-20.md`)

## Symptom

`test/03_system/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl`, `it "uses
nogc_sync_mut for sync GC metadata"` fails:

```
✗ uses nogc_sync_mut for sync GC metadata
  semantic: unknown static method with_heap_size on class GcConfig
```

even though `src/lib/nogc_sync_mut/gc.spl:139` defines exactly that method,
and `GcConfig.default()` (the impl block's *first* static method,
immediately above `with_heap_size`) resolves and runs fine through the same
import.

## Minimal repro (standalone, `bin/simple run`, not just `test`)

```simple
use std.nogc_sync_mut.gc.{GcConfig, GcStats}

fn main():
    val config = GcConfig.with_heap_size(20 * 1024)
    print("young_size={config.young_size} old_size={config.old_size}")
main()
```

`bin/release/x86_64-unknown-linux-gnu/simple run <this file>` prints:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: ArenaAllocator while lowering GcHeap.with_config
error: semantic: unknown static method with_heap_size on class GcConfig
```

(`GcHeap.with_config`, a method on a *different* class declared later in
the same file, references `ArenaAllocator` — imported via `gc.spl`'s own
`use std.allocator.{ArenaAllocator, SlabAllocator}`, a bare/un-tiered
import that itself doesn't resolve correctly in every import context —
separately worth qualifying to `std.nogc_sync_mut.allocator`, but doing so
does NOT fix this bug: it just changes which "Unknown variable" fires.
Confirmed with an alternate trigger after qualifying both bare imports in
`gc.spl` — `HIR lowering error: Unknown variable: panic while lowering
RuntimeValue.from_ptr` — same downstream symptom, same missing
`with_heap_size`.)

## Isolation (rules out gc_sync_mut / cross-tier collisions)

- Removing `src/lib/gc_sync_mut/gc.spl`, `src/lib/gc_async_mut/gc.spl`, and
  `src/lib/nogc_async_mut/gc.spl` simultaneously (the other tiers' full
  `GcConfig` re-definitions) does **not** fix the repro — ruling out a
  duplicate-struct/bare-name-registry collision across variant tiers
  (the mechanism documented in
  `doc/08_tracking/bug/duplicate_type_name_collision_audit_2026-07-17.md`).
- Qualifying `gc.spl`'s two bare imports (`std.allocator` →
  `std.nogc_sync_mut.allocator`, `std.runtime_value` →
  `std.nogc_sync_mut.runtime_value`) does **not** fix it either — it only
  moves the HIR-lowering error to a different unresolved identifier
  (`panic` inside `RuntimeValue.from_ptr`), confirming the JIT-failure
  trigger is incidental/environment-dependent, not the actual defect.
- A hand-copied, byte-identical `struct GcConfig`/`impl GcConfig` block
  (lines 114-144 of `gc.spl`) works perfectly **in isolation** (no JIT
  failure anywhere in that tiny file) — `default()` and `with_heap_size()`
  both resolve and run correctly. The bug requires *some other*
  declaration in the same whole-program closure to trip a JIT/HIR-lowering
  error; it is not intrinsic to `GcConfig` itself.
- Concatenating the exact, unmodified `GcConfig` block (lines 114-144) with
  the exact, unmodified `class GcPtr<T>:` block (lines 568-637 — a generic
  class whose methods reference an undefined-in-this-slice `GcHeap` type)
  reproduces the bug reliably: same "unknown static method with_heap_size"
  after a JIT-fallback log line.
- A fully synthetic minimal repro (two unrelated top-level declarations,
  one a free function referencing an undefined variable to force a JIT
  failure) did **not** reproduce — the failure must occur while lowering
  another **class's method** (e.g. `GcHeap.with_config`), not a bare free
  function, to trigger the loss. Not narrowed further than that within this
  triage task's scope.

## Root-cause audit (2026-07-23)

The original partial-registration hypothesis is disproven in current source.
Both interpreter registration paths iterate every method in an `impl` block:
`interpreter_eval.rs` for the flattened entry module and
`interpreter_module/module_evaluator/evaluation_helpers.rs` for imported
modules. Those loops predate this report (2026-07-04), and the JIT fallback
reloads and evaluates the module through the former path. The HIR imported-type
warning that resolved `std` relative to `/tmp` was a separate wiring bug:
`run_file_jit` omitted the existing bounded temporary-source project hint. It
now passes that hint to `lower_with_context_and_project_hint`.

`interpreter_constructor_test.rs::impl_registers_every_static_method` now pins
the precise source invariant with two distinct static methods and calls the
second. No speculative registry reset was added because the current JIT
lowering path does not mutate the interpreter registries.

## Why not fixed here

The deployed binary still needs a controlled rebuild before this report can be
closed. Its failure does not justify a new compiler mutation when the current
source already contains the required all-method registration behavior.

## Status

Source invariant pinned; deployed-binary verification pending. The exact
`test/03_system/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl`
assertion remains unchanged and red on the stale deployed binary.
