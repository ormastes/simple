# `<<<>>>` evaluates to Nil and E2 stream/event externs are undefined on the deployed seed (2026-08-25)

Plan: `doc/03_plan/lib/gpu/gpu_cuda_hardening_plan_2026-08-25.md` rows E2, E3.
Status: FIXED in source (Rust runtime + interpreter + std.cuda/std.io wrappers),
**RED on every deployed binary until the seed is rebuilt and redeployed.**

## Defects

1. **E3** — `compiler/src/interpreter/expr/calls.rs:95` evaluated
   `Expr::KernelLaunch` to `Value::Nil`, so `k<<<grid: g, block: b>>>(args)`
   ran nothing and every kernel test stayed green while doing no work.
   Now desugars to `gpu_launch_emulated(grid, block, \ -> k(args))`
   (std.gc_async_mut.gpu_ops); without that import it is a hard error
   `kernel launch `<<<>>>` requires `use std.gc_async_mut.gpu_ops.*` in interpreter mode`.
2. **E2** — the runtime had no stream/event/async-copy entries; std.cuda's
   `CudaStream` was a fake handle-0 struct. `runtime/src/cuda_runtime.rs` now
   exports `rt_cuda_stream_{create,destroy,synchronize}`,
   `rt_cuda_event_{create,destroy,record,synchronize,elapsed_ms,elapsed_ns}`,
   `rt_cuda_memcpy_{htod,dtoh}_async`, `rt_cuda_launch_kernel_ex` (+ `-3`
   no-cuda twins) and the interpreter dlopen table mirrors them.

## Reproduce specs (RED pre-fix, GREEN on the private build)

| spec | 08-23 seed (`goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`) | private build (origin tip + E2/E3) |
|---|---|---|
| `test/01_unit/lib/gpu/kernel_launch_syntax_interpreter_spec.spl` | `Results: 5 total, 0 passed, 5 failed` | `Results: 5 total, 5 passed, 0 failed` |
| `test/01_unit/lib/gpu/cuda_streams_events_spec.spl` (SIMPLE_CUDA_TEST=1) | `Results: 5 total, 2 passed, 3 failed` (`unknown extern function: rt_cuda_stream_create`) | `Results: 5 total, 5 passed, 0 failed` |
| `test/01_unit/lib/gpu/cuda_public_surface_spec.spl` | 2 failed (same unknown extern) | `Results: 4 total, 4 passed, 0 failed` |

The device-free arity case in `cuda_streams_events_spec.spl` greps
`src/compiler_rust/runtime/src/cuda_runtime.rs`; until the Rust change lands in
the shared tree it is RED there too. `SIMPLE_CUDA_RUNTIME_SRC=<tree>` points it
at another checkout.

## Unblock condition

Land the `src/compiler_rust` change, rebuild the seed, redeploy
`bin/release/<triple>/simple`. Until then the shared tree declares externs no
deployed binary defines, so std.cuda stream/event callers see
`unknown extern function` on the seed.

## Known follow-ups (not fixed here)

- `src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl:92` declares
  `rt_cuda_event_create()` with 0 args; the runtime export takes `flags: i64`.
  The interpreter treats the flag as optional (default 0); a native/JIT call
  through that declaration passes an undefined flags word. Fix in that lane.
- `rt_cuda_memcpy_htod_array_fn` (`interpreter_extern/gpu.rs`) calls the runtime
  crate directly with no dlopen fallback, so on a build WITHOUT the `cuda` cargo
  feature (the private build) it returns -3 and
  `cuda_io_sffi_extern_abi_spec.spl` "round-trips host bytes" reads zeros.
  Pre-existing; the deployed seed (built with `cuda`) passes it.
