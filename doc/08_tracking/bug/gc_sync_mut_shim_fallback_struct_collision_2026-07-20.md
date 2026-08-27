# `src/lib/gc_sync_mut/` exists (869 files) despite being documented as "not a public variant directory"

**Date:** 2026-07-20
**Scope:** `src/lib/gc_sync_mut/**` (existence itself)
**Severity:** low-medium — breaks one assertion in `test/feature/lib/gc_parity/gc_module_loader_spec.spl`; architectural drift, not a crash

## Symptom

`test/feature/lib/gc_parity/gc_module_loader_spec.spl`, `it "does not
expose an unimplemented gc_sync_mut family"` fails:

```
✗ does not expose an unimplemented gc_sync_mut family
  expected true to equal false
```

The spec asserts `test -d src/lib/gc_sync_mut` is **false**. It is
**true**: the directory exists with 869 tracked files (allocator, gc, gpu,
gpu_driver, gpu_runtime, http, mimalloc, spec, test_runner, torch, web,
websocket, ...) — not a stub. `.claude/rules/structure.md` documents only 5
public variant tiers (`common`, `nogc_sync_mut`, `nogc_async_mut`,
`gc_async_mut`, `nogc_async_mut_noalloc`); `gc_sync_mut` is deliberately
excluded, and this spec's own docstring says so explicitly ("gc_sync_mut/
is intentionally not a public variant directory... until a future family
is explicitly designed").

## Likely origin

`git log --diff-filter=A -- src/lib/gc_sync_mut` shows the directory was
reintroduced wholesale by `369a3725bbe "revert: restore 13,174 files
mass-deleted by e3e22d19da torn-working-copy commit"` — consistent with the
project's known "mass-revert un-deletes something that was deliberately
removed" failure class (`feedback_stale_wc_reverts_pushed_fixes.md`), not a
deliberate, currently-endorsed design decision. 21 commits total touch the
tree, the most recent being unrelated `nvme_fw_rv32` work that happened to
land files under it.

## Not the cause of the sibling spec's failure

Initially suspected this shim (`src/lib/gc_sync_mut/gc.spl`, a 15-line
`use std.gc.{...}` re-export relying on the module loader's fallback chain)
was also responsible for `nogc_sync_mut_contract_spec.spl`'s
`GcConfig.with_heap_size` failure. Disproven by direct test: moving
`gc_sync_mut/gc.spl` (and, for completeness, `gc_async_mut/gc.spl` and
`nogc_async_mut/gc.spl` — the other tiers' full `GcConfig` implementations)
out of the tree and re-running the repro still reproduces the exact same
error. That failure has a different, unrelated root cause — see
`doc/08_tracking/bug/jit_fallback_drops_second_static_method_registration_2026-07-20.md`.

## Why not fixed here

Deleting/renaming `src/lib/gc_sync_mut/` (869 files, includes `gpu/`,
`gpu_driver/`, `gpu_runtime/`, `torch/`) is out of this triage task's scope
per hard constraint ("NEVER touch GPU/CUDA/torch/ml/ui/wm/os sources"), and
is a large architectural call that shouldn't be made as a side effect of a
test-triage pass. Filing instead so an owning session can decide: (a)
delete `gc_sync_mut/` entirely (matches the documented "not implemented"
design + this spec's assertion), or (b) if `gc_sync_mut` is now intended to
be a real 6th family, update `.claude/rules/structure.md` + this spec's
docstring/assertion to match.

## Status

Not fixed (spec still red on the deployed binary). Left as-is per "never
weaken/delete the assertion to force green" — the assertion is correct per
the documented architecture; the source tree is the thing that's wrong.
