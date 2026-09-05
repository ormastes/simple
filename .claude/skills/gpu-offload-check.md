# GPU Offload Check Skill — scan, read, refactor

Verify web/2D renderer code is GPU-offloadable and burn down the blocked
inventory. Policy: **inventory mode first** (warnings/ratchet, not errors).

## 1. Run the scanner

```bash
bin/simple run src/app/gpu_lint/gpu_runnable_scan.spl
```

- Scans top-level `.spl` of `src/lib/gc_async_mut/gpu/engine2d` and
  `src/lib/gc_async_mut/gpu/browser_engine` (hardcoded in `main()`).
- Stdout gives a ≤30-line summary. The full report is `file_write`n to a
  hardcoded `out_path` near the end of `main()` — repoint it to your
  scratchpad before running.

## 2. Read the report

- Header caveats first: name-match call graph → same-name defs merge
  (false positives), cycle marking over-approximates.
- `Blocked names N / M` and `Tainted overloaded names` are the ratchet
  numbers — never let them rise in a change you land.
- `Per-root verdicts` prints the FIRST blocking chain per root, e.g.
  `clear -> ffi-call:webgpu_sffi_compute_draw at ...`. Fix the named
  construct at the named file:line, re-run, repeat.
- Overload-taint rule: if ANY def of name N is blocked, every caller of N is
  tainted. Either fix all defs of N or rename the offloadable one apart.
- Whitelist = `vulkan_*`/`cuda_*`/`vk_*`/`*vulkan_sffi*`/`*cuda_sffi*`
  intrinsics. Everything else `*sffi*`/`ffi_*`/`rt_*`/`extern_*` is banned.
  Banned constructs: string ops, interpolation, list `.push`, Dict use,
  closures, higher-order calls, print, io, recursion/cycles.

## 3. Refactor pattern: core/shell split (AOP-style)

For each blocked chain, do NOT delete logging/formatting — separate concerns:

1. **Core:** extract the arithmetic/pixel/index logic into a new function
   using only scalars, fixed arrays, and whitelisted GPU intrinsics. No
   strings, no alloc, no print, no recursion (convert to loops).
2. **Shell:** the original function keeps its signature and host concerns
   (formatting, provenance strings, logging, alloc), and calls the core.
3. Re-point the offload root (or its chain) at the **core**; the shell stays
   host-side. Name cores distinctly (avoid overload taint), e.g.
   `_x_core` / `x_device`.
4. Re-run the scanner; the root must flip to OFFLOADABLE and the blocked /
   tainted counts must not rise.

## References

- Design + staged plan (scanner now → `@gpu_runnable` semantic pass later):
  `doc/01_research/ui/rendering/gpu_runnable_compile_time_verification.md`
- Feature expert (inventory numbers, phase-audit reality):
  `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`
- Plan hook: `doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md`
