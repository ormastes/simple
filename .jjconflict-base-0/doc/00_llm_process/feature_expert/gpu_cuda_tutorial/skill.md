# Feature Expert: gpu_cuda_tutorial (CUDA/GPU programming hardening + tutorial)

## Role

Own the user-facing GPU programming surface of Simple: the `std.cuda` / `std.io` CUDA SFFI /
`gpu_ops` APIs, the CUDA workbook port under `examples/08_gpu/simple_cuda_example/`
(submodule `ormastes/simple_cuda_example`, parallel to `ormastes/cuda_exercise`), the
same-code/three-backend example `examples/08_gpu/backends/`, and the md-embedded sdoctests
that keep the READMEs honest.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)

## Feature Links

- Guide: `doc/07_guide/lib/gpu_3d/cuda_gpu_programming.md` (practical), `gpu_api.md` (reference),
  `gpu_backend_hardening.md`
- Examples: `examples/08_gpu/README.md`, `examples/08_gpu/backends/README.md`,
  `examples/08_gpu/simple_cuda_example/README.md`
- Source: `src/lib/nogc_sync_mut/cuda/`, `src/lib/nogc_sync_mut/io/cuda_sffi.spl`,
  `src/lib/gc_async_mut/gpu_ops.spl`, `src/lib/nogc_sync_mut/gpu_runtime/mod.spl`,
  `src/lib/gc_async_mut/gpu_lane/{cuda,vulkan,metal}_*`, `src/lib/nogc_sync_mut/notebook/gpu_config.spl`
- Specs: `test/01_unit/lib/gpu/*_spec.spl` (extern ABI, typed transfer round-trip, backend probe,
  public surface, Vulkan honesty), `examples/08_gpu/backends/backends_spec.spl`,
  `test/01_unit/compiler/mdsoc/gpu_layer_facets_spec.spl`, `test/03_system/gpu_lane/*`
- Layer experts: `../../layer_expert/compiler_driver/skill.md` (seed dispatch),
  `../board_vulkan/skill.md`, `../gpu_remote_lanes/skill.md`

## Handoff notes (2026-08-25)

Fixed this pass (all with reproduce specs): phantom `rt_cuda_*` extern ABI in `io/cuda_sffi.spl`
(17/24 externs did not exist); `gpu_upload/download_*` passing the interpreter's `Vec<Value>`
pointer as raw bytes (SEGV ≥ 2048 f32); `gpu_runtime` device count gated on PyTorch;
`std.gpu` `Context(backend: Vulkan)` silently running on CUDA; `cuda_jit_lane_executor` missing
the HIR `items` import; `85.mdsoc/cross_query.spl` missing `construct_types` imports.

Open, filed under `doc/08_tracking/bug/*_2026-08-25.md`:
`std.gpu` package import binds to the no-CUDA stub (`(0,-3)`); Vulkan init fails under `run` but
not `test`; Vulkan VM lane returns exit 0 after a CUDA lane in one process; seed cross-module
method collision blocks `cuda_jit_hello` HIR lowering; top-level `arr[i] = …` in a loop dropped;
`<<<grid:, block:>>>` has no `stream:` slot.

Constraints: real-hardware asserts behind `SIMPLE_CUDA_TEST=1`; one spec per `bin/simple test`
invocation; a nested `.git` under `examples/` makes the seed resolve the stdlib from another
worktree — park it while verifying; the md doctest runner only checks exit 0, so end blocks with
`>>> assert …`.

Verification: `SIMPLE_CUDA_TEST=1 bin/simple test test/01_unit/lib/gpu/<one>_spec.spl`;
`bin/simple test examples/08_gpu/backends/backends_spec.spl`; per module
`bin/simple run <main.spl>`, `bin/simple test <spec.spl>`, `bin/simple test <README.md>`.
