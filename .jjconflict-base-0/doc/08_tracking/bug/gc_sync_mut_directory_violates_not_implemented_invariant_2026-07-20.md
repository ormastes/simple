# `src/lib/gc_sync_mut/` exists with real content, violating the "not a public variant directory" invariant the spec + structure.md both encode

**Date:** 2026-07-20
**Component:** repo layout — `src/lib/gc_sync_mut/` vs.
`test/feature/lib/gc_parity/gc_module_loader_spec.spl` and
`.claude/rules/structure.md`'s documented lib family list.
**Severity:** Low — architectural-invariant/hygiene mismatch, not a runtime
crash.

## Symptom

`test/feature/lib/gc_parity/gc_module_loader_spec.spl`, example
`"does not expose an unimplemented gc_sync_mut family"`, fails under
`bin/simple test`:

```
Module Resolution Fallback
  when importing array utilities from common
    ✓ accesses array utilities after migration
  when verifying omitted sync GC family
    ✗ does not expose an unimplemented gc_sync_mut family
```

The spec's `it` block:

```simple
it "does not expose an unimplemented gc_sync_mut family":
    """
    The runtime-family matrix marks gc_sync_mut as not implemented.
    The source tree should not contain a stub family that reverses
    the no-GC-first direction.
    """
    expect(_has_gc_sync_mut_source_dir()).to_equal(false)
```

asserts `src/lib/gc_sync_mut` does not exist. It does exist, and is not a
stub: `ls src/lib/gc_sync_mut` lists real subdirectories/files
(`allocator.spl`, `array.spl`, `gc.spl`, `db/`, `gpu/`, `gpu_driver/`,
`gpu_runtime/`, `hooks/`, etc. — ~229 lines of `.spl` across the flat files
alone). Sampled contents:
- `gc.spl` — deliberate re-export facade: `# GC Re-Export for gc_sync_mut ...
  This module re-exports it so gc_sync_mut code can import GC types
  directly.` (`use std.gc.{GcHeap, GcConfig, ...}` + `export ...`)
- `array.spl` — `@allow(star_import) # reason: compatibility facade,
  re-exports backing family symbols` / `export use nogc_async_mut.array.*`
- `allocator.spl` — a real `class GcAllocator` (not a re-export) implementing
  a GC-backed `Allocator` trait interface (`new`, `with_heap`, and free
  functions `gc_allocator_new`/`gc_allocate`/`gc_deallocate`/
  `gc_reallocate`/`gc_total_allocated`).

## Root cause / open question

`.claude/rules/structure.md`'s documented `src/lib/` family list is:
`common/`, `nogc_sync_mut/`, `nogc_async_mut/`, `gc_async_mut/`,
`nogc_async_mut_noalloc/` — it does **not** list `gc_sync_mut/` as a
supported family, matching this spec's docstring ("gc_sync_mut is
intentionally not a public variant directory... until a future family is
explicitly designed"). Yet the directory is present with deliberate,
commented compatibility-facade code, not leftover cruft from a revert —
someone built real (if thin) `gc_sync_mut` scaffolding without updating
either `structure.md` or this spec.

This is a genuine inconsistency between committed code and the documented
architecture invariant, not a case of "test uses a renamed API" — fixing it
requires an architectural decision (delete `gc_sync_mut/` to restore the
invariant, or formally adopt it and update `structure.md` + this spec's
docstring together), which is out of scope for a mechanical test-triage
pass. The assertion was intentionally left unchanged (not weakened) per the
never-weaken rule.

## Notes

- Spec left RED as-is: `expect(_has_gc_sync_mut_source_dir()).to_equal(false)`
  was NOT flipped to `true` or deleted — that would just silence a real
  architecture-drift signal.
- Affected: `test/feature/lib/gc_parity/gc_module_loader_spec.spl` (1 of 2
  examples fails; the array-utilities-from-common example in the same file
  passes cleanly).
