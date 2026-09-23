# GPU FFI loader probes Linux sonames on macOS (and `spl_dlopen` raises where `DynLib.load` expects nil)

- Status: SOURCE FIXED (2026-09-21); macOS on-device validation pending
- Found: 2026-09-19
- Component: `src/lib/nogc_sync_mut/gpu/engine2d/ffi_dispatch.spl` (`gpu_lib_candidates`, :60-84), `src/lib/nogc_sync_mut/sffi/dynamic.spl` (:121-128), seed runtime `spl_dlopen`
- Binary: deployed Rust seed (macOS aarch64)

## Observation

`gpu_lib_candidates()` selects `.dylib` candidate names only when the env var `SIMPLE_OS_TYPE == "Darwin"`, but **nothing in the repo ever sets `SIMPLE_OS_TYPE`** (grep over src/scripts/bin finds zero setters; it is unset in the environment). Result: even on this macOS host the loader probes Linux sonames (`libvulkan.so.1`, `libcuda.so.1`), finds nothing, and:

- per the documented comment at `dynamic.spl:121-128`, the interpreter lane's raw `spl_dlopen` **raises and aborts** on an unresolvable bare soname instead of returning a handle — so `DynLib.load`'s nil path is unreachable and the in-spec `if ffi == nil` guard never gets control;
- Simple has no try/catch (`src/lib/nogc_sync_mut/spec.spl:17`), so no spec-side guard is possible.

Concrete impact (2026-09-19, macOS host with Vulkan installed at `/opt/homebrew/lib/libvulkan.dylib`):
- `test/01_unit/lib/gpu/engine2d/ffi_cuda_spec.spl` "loads the installed CUDA driver": `runtime: spl_dlopen failed for 'libcuda.so.1'` (host has no CUDA — expected unavailable, but should be a clean nil, not a raise);
- `test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl` ledger/`is_available`: `runtime: spl_dlopen failed for 'libvulkan.so.1'` — the run never tries the installed `.dylib` names.

## Fix direction

1. Platform detection at the source: derive the Darwin branch from an env that IS set (e.g. `rt_platform_os()` / uname-based runtime query) or set `SIMPLE_OS_TYPE` in the CLI/runtime entry; do not depend on an unset env var.
2. Seed-side (record-only; seed is bootstrap-only per project rules): `spl_dlopen` should return nil/raise only at the `DynLib.load` boundary so the documented nil path is reachable — or the .spl layer should probe with a non-raising variant first.
3. Re-run the two specs above; a clean `ffi == nil` on a no-device host is the acceptance signal (and `ffi != nil` using the homebrew Vulkan on this host).

## Related

- `gated_specs_are_tautology_shells_2026-08-09` (the lane that surfaced this; its 2 remaining reds are this defect)

## 2026-09-21 source repair and verification

Both `ffi_dispatch.spl` and its `sffi_dispatch.spl` twin now derive candidates
from `std.io_runtime.platform_name()`, whose runtime implementation returns
`macos` on Apple hosts. Candidate mapping is tested independently of host OS,
and a live host case checks the same runtime identity path. The checked loader
now returns an error immediately when `spl_dlopen_checked` returns a nonzero
status. It retains the direct-return fallback only for status zero with an
unobserved output handle, the documented interpreter writeback-loss case.

The focused `ffi_dispatch_platform_spec.spl` was run on Linux with the shared
`/home/yoon/dev/simple/bin/simple`, which identified itself as a **Rust-built
bootstrap seed**, in interpreter mode with `SIMPLE_LIB=src`. Its pre-edit RED
had two helper-existence failures (`gpu_lib_candidates_for_os` did not yet
exist) and one observed missing-bare-soname `spl_dlopen` raise. The helper
failures are test-first evidence, not a reproduction of Darwin selection on a
macOS host. After the source repair the spec passed 4/4 on that same seed.
This proves the candidate mapping and nil failure path only under the Linux
seed interpreter. The admitted pure-Simple runtime and the originally affected
macOS host remain unverified; run the focused spec plus the existing CUDA and
Vulkan specs on macOS before closing this bug.

The public `gpu_lib_candidates`, `try_load_gpu_lib`, `DynLib.load`, and
`DynLib.load_checked` signatures are unchanged. SimpleOS keeps the static
selection from `SIMPLE_OS_KERNEL`; the candidate lookup is only used on hosted
dynamic paths. SOSIX app and host interfaces are untouched.
