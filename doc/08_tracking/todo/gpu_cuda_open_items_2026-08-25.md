# GPU/CUDA open items after the 2026-08-25 hardening landing

Landed: `8a291217121` (simple) + `b58990d` (simple_cuda_example).
Plan: `doc/03_plan/lib/gpu/gpu_cuda_hardening_plan_2026-08-25.md`.
Guide: `doc/07_guide/lib/gpu_3d/cuda_gpu_programming.md`.

Everything below is either a filed defect someone must fix, or a deliberate deferral with its
interim spelling recorded. Nothing here is "nice to have" — each blocks a capability a user of
the GPU surface will reach for.

## Blocked on a seed redeploy (code landed, no deployed binary carries it)

| item | evidence |
|---|---|
| CUDA streams / events / async copies (`rt_cuda_stream_*`, `rt_cuda_event_*`, `rt_cuda_memcpy_*_async`, `rt_cuda_launch_kernel_ex`) | green on a private build; `nm` shows 0 of these in the deployed seed |
| `kernel<<<grid, block>>>(args)` executing instead of evaluating to nil | `kernel_launch_syntax_interpreter_spec.spl` 5/5 private, 0/5 deployed |

Until a redeploy, `std.cuda` stream paths raise `unknown extern function` on the deployed binary.

## Defects filed (`doc/08_tracking/bug/*_2026-08-25.md`)

1. `origin_main_not_test_runnable_env_access_host_parse` — a fresh worktree of `main` cannot run
   `bin/simple test` at all (`src/app/io/env_access_host.spl`: `expected Comma, found Pub`). No
   pre-push guard parses `.spl`, so this class lands green. **Highest priority: it invalidates
   test evidence taken from any tree that differs from `main`.**
2. `std_gpu_package_import_binds_cuda_externs_to_nocuda_stub` — `use std.gpu.*` reports 0 devices
   and cc `(0, -3)` while the direct module import sees both GPUs. Every doc that says
   `use std.gpu.*` is wrong until this is fixed.
3. `vulkan_instance_init_fails_under_run_but_not_test` — same code, same host, different entry point.
4. `vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process` — second backend in one process
   returns `ok=true` with no sentinel and no records: a silent wrong answer, not a skip.
5. `cuda_jit_hello_lane_lower_module_missing_import` — import fixed; the remaining half is the
   seed's cross-module member resolution (`ParserModule has no field named friends`).
6. `top_level_array_index_assign_in_loop_silently_dropped` — module-level `arr[i] = …` in a loop
   is a no-op, which silently breaks sdoctest blocks.
7. `simd_lane_ops_reject_f32_cast_values` — `rt_simd_mul_f32x4` rejects `Float32`, so `std.simd`
   f32 lane ops are unusable on genuinely-f32 data.
8. `kernel_launch_grammar_no_stream_slot` — deferred, see below.
9. `seed_redeploy_breaks_test_runner_accessor_rewrite_parse` — deployment hygiene.
10. `preexisting_test_tree_divergence_stepped_over_gpu_landing` — record of the divergence backlog
    this landing stepped over with a delta-PASS.

## Deferred by decision (TODO markers in source, picked up by `todo-scan`)

- `src/compiler_rust/parser/src/expressions/postfix.rs` — `<<<…>>>` has no `stream:` / `shared:`
  slot. The runtime supports both; `cuda_launch_on` is the interim spelling. Deferred because the
  self-hosted AST variant `KernelLaunch(Expr, Expr, Expr, [CallArg])` is positional.
- `src/lib/gc_async_mut/gpu_ops.spl` — the CPU executor runs one work-item at a time, so
  `gpu_syncthreads` is a no-op and shared-memory exchange is unmodelled; tiled reduction/transpose
  kernels cannot be verified device-free.
- `src/lib/nogc_sync_mut/io/cuda_sffi.spl` — no `cudaMemcpyPeer`; multi-GPU transfers stage
  through host memory.

## Not attempted (stated so the gap is not mistaken for coverage)

CUDA graphs, IPC, virtual-memory API, cooperative groups, dynamic parallelism, tensor cores/WMMA,
and the vendor libraries (cuBLAS/cuFFT/cuRAND/cuSPARSE/cuDNN/GPUDirect Storage). The tutorial
modules for these are README-only and say which Simple facility, if any, is the honest equivalent.

## Why `todo_db.sdn` is not regenerated in this change

The three TODO markers above are in the source in the exact form `bin/simple todo-scan` matches
(`# TODO:` / `// TODO:` at the start of a trimmed comment line — `src/app/todo_scan/main.spl:96`),
so the next successful scan will pick them up. The generated database is **not** included here:

- Running `todo-scan` against a clean `origin/main` worktree FAILS — the same
  `src/app/io/env_access_host.spl` parse error that makes `main` not test-runnable
  (`doc/08_tracking/bug/origin_main_not_test_runnable_env_access_host_parse_2026-08-25.md`).
- Running it against the shared working tree "succeeds" but produces a db with **741 fewer lines
  than origin's** — that tree is behind on many files, so committing that output would silently
  delete other sessions' TODO entries. Per `.claude/rules/vcs.md` ("sync must never clobber"),
  that is worse than not regenerating.

Regenerate once `main` parses again: `bin/simple todo-scan` from a clean checkout.
