# gpu_solver.spl rt_cuda_launch_kernel declaration has the wrong argument list

Found while canonicalising the return shape in PR #12367 (shape fixed there; arity not).

`src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl` declares
`rt_cuda_launch_kernel(func: i64, gx, gy, gz, blk_x, blk_y, blk_z, shared_mem: i64, args: [i64]) -> i64`.
The real extern (C `src/runtime/runtime_dynload.c`, Rust `interpreter_extern/gpu.rs`, and the
other .spl declarations, e.g. `nogc_sync_mut/cuda/sffi.spl`) is
`rt_cuda_launch_kernel(module: i64, func_name: text, grid_x, grid_y, grid_z, block_x, block_y, block_z, args_ptr: i64) -> i64`.

The solver passes a function handle from `rt_cuda_get_function` and an `[i64]` array, so calls
bind to the wrong ABI (the two dispatch call sites at ~683 and ~713 ignore the result, so the
failure is silent). No CUDA hardware on the dev host; fix needs: switch the solver to the
module/name launch (or the `_ex` variant for shared memory), pass a device args pointer, check
the returned status, and add a shape/arity spec. Verify on a CUDA host.

Status: open.
