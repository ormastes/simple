# Unqualified `std.gpu.engine2d.metal_session` import can resolve to the wrong memory-model variant
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Verification 2026-11-25 (p3-bam lane, Windows worktree) — symptom dead, closing

Binary: worktree-tracked `bin/simple.exe` (38,403,072 bytes, x86_64 Windows),
`SIMPLE_LIB=src`, branch `work/p3-bam-20261125` off `release/1.0.0`.

The premise of this record no longer holds: the `nogc_sync_mut` variant
(`src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl`) no longer defines
`MetalSession` at all — it now exports `MetalPipelineCache` (:16) and
`MetalComputeSession` (:73). `MetalSession` exists only in the `gc_async_mut`
variant (`src/lib/gc_async_mut/gpu/engine2d/metal_session.spl:36`), so there
is no same-named class with a divergent method set left to mis-resolve to.

Live probes from a scratch script outside either variant directory:

- `use std.gpu.engine2d.metal_session.{MetalSession}` (unqualified) now fails
  LOUDLY at compile time: `[use-warning] 'MetalSession' is named in ... but
  module '.../nogc_sync_mut/gpu/engine2d/metal_session.spl' does not provide
  it`, then `error: semantic: ... variable 'MetalSession' not found`. The
  original silent failure mode (construction succeeds, then `method 'init'
  not found` at the first call) can no longer occur — the wrong-variant
  import is rejected up front with a diagnostic naming the module.
- `use std.gc_async_mut.gpu.engine2d.metal_session.{MetalSession}`
  (fully-qualified, the documented workaround) resolves and constructs:
  `MetalSession.create("offscreen")` prints `created`.

Effectively this is fix option (a) from the Suggested-fix section, arrived at
by class-name divergence plus the use-warning diagnostic rather than by an
ambiguity error. No production caller was ever affected. **Status: CLOSED.**
