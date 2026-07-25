# Metal `newFunctionWithName` cannot find a genuinely-new kernel appended to `_engine2d_msl()`

> **STATUS: RESOLVED — NON-REPRODUCING (transient) — 2026-07-07.**
>
> Re-verified on the *identical* binary
> (`bin/release/aarch64-apple-darwin-macho/simple`, 2026-07-05 build) and the
> *identical* machine/OS (Apple M4, Darwin 25.5.0) through the *identical*
> production entry point (`MetalSession.init()`), and it does **not** reproduce:
>
> ```
> init=true pipe_indexed_fill=15 pipe_clear=4 pipe_blit=14 err_code=0   # 5/5 runs
> ```
>
> `pipe_indexed_fill` — the exact pipeline this report says fails with
> `newFunctionWithName: function not found` — is created successfully **every
> time** (5/5 separate-process `MetalSession.init()` runs, 2 compiles per run =
> 10/10 new-kernel pipeline creations). The negative-control from this doc (a
> byte-for-byte `kernel_clear` body under a brand-new name `kernel_test_dup`)
> also succeeds 3/3. Full mechanism analysis (runtime-compiled MSL, no baked
> `.metallib`, no Simple/Rust-layer cache) is in
> `scratchpad/metal_new_kernel_blocker.md`.
>
> The GPU path is therefore **real and proven**: `indexed_fill` is now proven
> **bit-exact CPU-vs-Metal through genuine `device_readback`** by a dedicated
> row in `scripts/check/check-engine2d-gpu-offload-evidence.shs` /
> `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl`
> (`indexed_fill: MATCH pixels=3072 source=device_readback`, checksum
> `1413576747` on both backends).
>
> **Most-plausible original cause (inferred from non-reproduction, unverified):**
> a one-off wedged state in macOS's out-of-process Metal shader-compiler service
> (`MTLCompilerService`), which handles `newLibraryWithSource`/
> `newFunctionWithName` off-process and is known to occasionally wedge for a
> login session after a crashed/killed compile — NOT a defect in Simple's code.
> No rebuild/redeploy is prescribed as "the fix" because nothing reproduced that
> a rebuild could be shown to fix. **If it recurs:** first re-run the gate in a
> fresh process before assuming a code defect; only reproducible recurrence
> would newly falsify this finding (then capture `metal_last_error()` +
> `lib.functionNames()`). Kept below as a historical record.
>
> ---

**Found:** 2026-07-07, while implementing the GPU-dict pilot (W1,
`doc/03_plan/ui/rendering/cpu_gpu_dual_algorithm_plan.md`), on macOS
arm64 (Darwin 25.5.0) against the deployed self-hosted binary
`bin/release/aarch64-apple-darwin-macho/simple` (built 2026-07-05).

## Symptom

Adding a **new** kernel function (any name not already present in the
compiled library) to the MSL source returned by
`src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl::_engine2d_msl()`
causes `MetalSession.init()` → `metal_sffi_create_compute_pipeline(device,
shader_lib, "<new kernel name>")` to fail with `metal_last_error() ==
"newFunctionWithName: function not found"`, even though:

- `metal_sffi_compile_shader()` returns a **nonzero** library handle (the
  MSL "compiles" without error as far as the runtime reports).
- The **same exact source text**, dumped to a file and compiled directly
  with Apple's own compiler (`xcrun -sdk macosx metal -c src.metal -o
  out.air`), succeeds with **zero diagnostics**, and `xcrun -sdk macosx
  metal-nm out.air` lists the new kernel function by name.
- All 11 pre-existing kernels (`kernel_clear` … `kernel_blit_image`)
  continue to resolve and dispatch correctly (verified via
  `scripts/check/check-engine2d-gpu-offload-evidence.shs`, which stays
  green: bit-exact CPU-vs-Metal, `device_readback` provenance, for every
  existing op).
- Requesting a **duplicate** pipeline for an **already-known** kernel name
  (e.g. `kernel_clear` a second time, as the 12th
  `create_compute_pipeline` call in the same session) succeeds.

## Isolation performed

- Ruled out MSL syntax: `xcrun metal` compiles the extracted source clean.
- Ruled out total source size as the sole variable: shrinking the new
  kernel to a single trivial one-line body (`fb[tid] = 1u;`, no new
  structs, ~150 bytes) still fails; a byte-for-byte copy of an
  **already-existing** kernel body (`kernel_clear`'s body) under a **new**
  name (`kernel_test_dup`) also fails.
- Ruled out a hard pipeline-count limit: the 12th `create_compute_pipeline`
  call succeeds when it names an **existing** kernel.
- So the defect is specific to: *any newly-introduced kernel entry point*,
  independent of its size or content, resolved through this runtime's
  Metal FFI compile → pipeline-creation path on this machine/binary.

## Suspected root cause (unconfirmed)

Not isolated further given time constraints. Candidates, in order of
plausibility:

1. macOS's system Metal shader-compiler service
   (`MTLCompilerService`)/on-disk shader cache serving a stale compiled
   `MTLLibrary` keyed on something coarser than the full source text (no
   `~/Library/Caches/*metal*` directory was found on this machine, which
   weakens but does not rule this out — the cache may live elsewhere, e.g.
   inside a sandbox container).
2. A text-marshalling issue in the interpreter's `rt_metal_compile_shader`
   FFI boundary (`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs::
   rt_metal_compile_shader_fn` → `CString` → `metal_graphics_runtime.rs::
   compile_shader`) that silently serves/creates a differently-scoped
   `MTLLibrary` object for "new" content while `.len()` and downstream
   Rust-side string handling report the correct full text. Not confirmed;
   the code at `metal_graphics_runtime.rs:397-416` reads as a
   straightforward `CStr::from_ptr` → `NSString` → `newLibraryWithSource`
   call with no caching visible at that layer.

## Impact on the GPU-dict pilot

None of the CPU-lane oracle work, the capability/honesty wiring, or the
loud-fallthrough contract depends on this working. `MetalBackend.capability()`
correctly reports `indexed_fill` as **not accelerated**
(`session.pipe_indexed_fill == 0` on this machine), so
`MetalBackend.indexed_fill()` takes the design's §3.4 loud-fallthrough path:
CPU-lane mirror result stands, `gpu_frame_complete` is set `false`, no crash,
no wrong pixel is ever produced. The pilot is architecturally complete and
verified end-to-end on the CPU lane; the GPU dispatch path is implemented per
the design and should be re-verified with `bin/simple test
test/02_integration/rendering/engine2d_gpu_offload_evidence.spl` (or a
dedicated indexed_fill row added there) on a machine/runtime build where this
defect does not reproduce, or once root-caused.

## Repro

```
# From a Simple script using MetalBackend directly:
var mtl = MetalBackend.create()
mtl.init(8, 8)          # true — session succeeds
mtl.capability()        # accelerated_ops == [] on the affected machine
                         # (session.pipe_indexed_fill == 0)
```

Minimal Rust-adjacent repro: append literally any new `kernel void
kernel_xyz(...)` to `_engine2d_msl()`'s embedded MSL string and observe
`metal_last_error()` after `create_compute_pipeline(device, lib,
"kernel_xyz")`.
