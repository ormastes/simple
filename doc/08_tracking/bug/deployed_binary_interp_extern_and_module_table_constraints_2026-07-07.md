# Deployed self-hosted binary: interpret-mode extern registration + baked module table constraints

## Status
Documented (platform facts, not a single fixable bug) — informs how new
runtime capability must be shipped until the underlying constraints change.

## Severity
Informational / process — repeatedly re-discovered during GPU-offload work
(#17, #28-A, #28-B); recording once here to stop re-deriving it per task.

## Summary

Two independent constraints on the deployed `bin/release/<triple>/simple`
binary (built via bootstrap, run in `SIMPLE_EXECUTION_MODE=interpret`) shape
how any new runtime capability can be added without a bootstrap rebuild:

**(a) Interpret-mode externs are a closed, build-time table.** `extern fn`
declarations only resolve if the interpreter's `insert_simple!`-registered
dispatch table (compiled into the Rust runtime) contains a matching entry.
JIT-table externs that exist in the Cranelift/LLVM backends do NOT
automatically become callable in interpret mode — `rt_array_data_ptr` is a
concrete example: it is a real runtime symbol, but interpret-mode calls to it
hard-error (`unknown extern function: rt_array_data_ptr`) on the deployed
binary, because interpret dispatch only consults its own table, not the
JIT/AOT symbol resolver. The same split applies to `rt_write_u32s_to_raw`
(one-call GPU pixel *upload*) vs `rt_u32s_from_raw` (one-call *download*):
both were added to the runtime, but at different times, so a given deployed
binary can have registered one and not the other. Treat "the symbol exists in
the Rust source" and "the symbol is callable from interpreted `.spl`" as two
separate facts that must each be verified against the actual deployed binary.

**(b) The module table is baked at build time.** The deployed binary's
`SIMPLE_LIB` module resolver enumerates a table built when that binary was
compiled. A brand-new `.spl` file added under `src/lib/**` after that build —
even one that is syntactically valid and correctly placed in the directory
structure — is invisible to it (`Cannot resolve module std.foo.bar`) until a
fresh bootstrap/deploy picks it up. This is why new capability cannot ship as
"just add a new stdlib module and `use` it": the deploy step, not the source
tree, is what makes a module resolvable.

## Empirical Probes (2026-07-06/07, task #28)

- Interpret-mode call to `rt_array_data_ptr(pixels)` on the deployed binary →
  hard error `unknown extern function: rt_array_data_ptr`, confirmed by direct
  probe script (not inferred from source reading).
- `draw_image`'s one-call upload path gated on `SIMPLE_ONE_CALL_READBACK`
  (shared with the download gate) hard-errored mid-frame with
  `unknown extern function: rt_write_u32s_to_raw` the first time a frame
  actually took the upload branch, while the paired *readback* one-call path
  (`rt_u32s_from_raw`, gated by the same flag) succeeded in the same run —
  proving the two externs are registered independently on this binary. Fixed
  by splitting the gate into its own flag, `SIMPLE_ONE_CALL_UPLOAD`
  (`src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`), so neither fast
  path can silently ride on the other's availability.
- A new sibling `.spl` module placed under an existing stdlib package (not a
  new top-level directory) and `use`'d from `backend_metal.spl` produced
  `Cannot resolve module` on the deployed binary with no rebuild; the same
  code inlined directly into an already-known, already-deployed module
  (`backend_metal.spl` itself) resolved and ran immediately. Confirms the
  module table, not file placement/syntax, is the gate.

## Consequence / Working Rule

New runtime capability that the deployed binary cannot already dispatch must
ship as an **SFFI sibling cdylib** (dlopen'd at runtime via
`spl_dlopen`/`spl_dlsym`/`spl_wffi_call_i64` — the sanctioned dynamic-loader
pattern, see `.claude/memory/ref_sffi.md`), with the `.spl`-side wiring
**inlined into an existing, already-deployed module** rather than split into
a new sibling `.spl` file. Concretely, task #28-B's bulk GPU pixel-upload path
(`src/runtime/spl_gpu_transfer/` cdylib + `bulk_upload_u32s` and its
`_bulk_*` globals) lives inline in `backend_metal.spl` for exactly this
reason — a separate `backend_metal_bulk_upload.spl` module would have been
invisible on the deployed binary until the next full redeploy. Do not
reintroduce a split without pairing it with an actual bootstrap/deploy step in
the same change.

## Related
- `.claude/memory/ref_sffi.md` — FFI patterns, dynamic loader details.
- `doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md` — GPU
  offload feature history (#17/#28-A/#28-B).
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` — both the
  `SIMPLE_ONE_CALL_UPLOAD` split-gate fix and the inline `spl_gpu_transfer`
  bridge live here.
