# Unqualified `std.gpu.engine2d.metal_session` import can resolve to the wrong memory-model variant

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Found:** 2026-07-08, incidental finding during the "new kernel not found"
blocker investigation (`engine2d_metal_new_kernel_pipeline_not_found_2026-07-07.md`).
**Severity:** low — real callers are unaffected (see below); this only bites a
throwaway repro script written outside a variant folder.

## Symptom

The stdlib ships two parallel per-memory-model variants of `metal_session.spl`
with **different method sets**:

| Variant | Path | `MetalSession` init method |
|---------|------|----------------------------|
| gc_async_mut  | `src/lib/gc_async_mut/gpu/engine2d/metal_session.spl`  | `me init() -> bool` |
| nogc_sync_mut | `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl` | `me init_device() -> text` (and a `MetalPipelineCache` class) |

A script that imports the **unqualified** path
`use std.gpu.engine2d.metal_session.{MetalSession}` from **outside** either
variant directory can resolve to the `nogc_sync_mut` variant, and then a call
to `session.init()` fails at runtime with `method 'init' not found` (that
variant only offers `init_device()`). Both variants share the same
`static fn create(mode: text) -> MetalSession` constructor, so construction
succeeds and the divergence only surfaces at the first method call.

## Why real callers are unaffected

- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` resolves
  `metal_session` **same-directory** (→ the `gc_async_mut` variant with
  `init()`).
- `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl` reaches it
  transitively through `std.gc_async_mut.gpu.engine2d.engine`, i.e. the
  fully-qualified `gc_async_mut` path.

So no production caller hits the wrong variant. This is purely a
resolution gotcha for ad-hoc scripts.

## Workaround

Always import the **fully-qualified** variant path from a standalone script:

```
use std.gc_async_mut.gpu.engine2d.metal_session.{MetalSession}   # has init() -> bool
```

(The step-2a probe `scratchpad/probe_pipe_indexed_fill.spl` does exactly this.)

## Suggested fix (not done here)

Unqualified `std.<...>.metal_session` resolution across memory-model variants
with divergent public method sets should either (a) be a resolution error that
names the ambiguous candidates, or (b) deterministically prefer the variant
matching the importing module's memory-model family. Filed as a record; not
fixed in the GPU-dict pilot change.

## Triage 2026-09-12
Older than 45 days; record itself notes real callers are unaffected (low severity edge case). Not re-run in this pass. Closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
