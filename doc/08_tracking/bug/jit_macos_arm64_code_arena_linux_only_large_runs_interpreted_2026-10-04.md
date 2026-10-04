# macOS arm64: JIT code arena is Linux-only, so every large `simple run` panics at finalize and re-runs interpreted

- **Filed:** 2026-10-04
- **Area:** Rust seed JIT (`vendor/cranelift-jit/src/memory.rs` local patch), driver hybrid splice, Vulkan runtime feature
- **Status:** OPEN — fix prototyped and measured, NOT landed (it exposes a second defect, below)
- **Related:** `jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md` (the Linux fix),
  `host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11.md`

## Symptom

On Apple Silicon (M4, macOS 26), `simple run src/app/ui_showcase/hosts/main_2d_gpu.spl`
compiles the whole module with Cranelift (~45 s, 6,368 functions, ~14 MB of code), then:

```
PANIC AArch64 direct call is 171797308 bytes away, out of the +/-128 MiB reach of `bl`,
and no veneer could be placed within range (JIT code arena exhausted or unavailable).
[engine-demotion] reason=jit-panic ...
[INFO] JIT panicked, falling back to interpreter
```

and the entire program then runs in the tree-walk interpreter. Measured (seed built from
`origin/main` 90c6e6ed27b + the array-repeat fix, Vulkan via MoltenVK):

| run | wall | max RSS | result |
|---|---|---|---|
| 2D GPU showcase, Vulkan, 320x240, 2 frames | 131-172 s | 2.4-2.6 GB | pass, interpreted |
| same at 3840x2160, 2 frames | >900 s (timeout) | 4.07 GB | did not finish |

## Root cause

The 2026-09-06 fix carves each JIT module's code out of one contiguous 128 MiB
arena, but every gate is `cfg(all(target_arch = "aarch64", target_os = "linux", ...))`.
On macOS the old heap allocator is still used, and Apple's allocator places one
module's code chunks ~171 MB apart. The arena high-water for this module is only
14,224 KiB of the 131,072 KiB cap, so the arena would fit it with room to spare.

## Prototype (works for the panic)

Widening the eight arena gates in `memory.rs` to
`any(target_os = "linux", target_os = "macos")` (the BTI `mprotect` gate at line 529
stays Linux-only) removes the panic: `SIMPLE_JIT_ARENA_STATS=1` reports
`arena[0] code high-water 14224 KiB, veneers 0 B` and the module runs JIT'd.
The seed is ad-hoc, linker-signed without hardened runtime, so the arena's
RW→RX `mprotect` is the same W^X sequence the heap path already uses.

Two build traps found doing it:
- `vendor/` is a cargo source-replacement directory, so cargo does **not** notice
  edits to vendored files: `cargo clean -p cranelift-jit --release` is required.
- `vendor/cranelift-jit/.cargo-checksum.json` must be updated with the new
  `src/memory.rs` sha256.

## Why it was not landed: it exposes the Vulkan stub split

Once the JIT actually runs, `Engine2D.create_with_backend_fast(w, h, "vulkan")`
returns the **cpu** backend under JIT but **vulkan** under the interpreter:

```
JIT:          backend=cpu
interpreter:  backend=vulkan
```

The default seed is built without the runtime `vulkan` cargo feature, so the
runtime exports `rt_vulkan_init` as a `not(feature = "vulkan")` stub returning 0.
JIT code resolves to that stub; the interpreter instead uses the dlopen bridge in
`compiler/src/interpreter_extern/gpu.rs` and reaches the real MoltenVK device.
Landing the arena alone would turn today's slow-but-passing Vulkan showcase into
`status=blocked reason=vulkan-device-unavailable` — a visible regression.

A second prototype routed the `rt_vulkan_*` family through the hybrid
interpreter splice when `rt_simple_gpu_provider_backend_bits() & 2 == 0`
(`driver/src/exec_core.rs`, the `unresolvable_externs` predicate). That made
`rt_vulkan_init` succeed under JIT, but session init then failed at
`shader-clear`: `sffi_vulkan.spl` picks the native `_array` ABI
(`rt_vulkan_compile_spirv_array`, `..._copy_to_buffer_array`,
`..._push_constants_array`, `..._readback_u32_array*`, 11 symbols) whenever
`rt_is_interpreter_runtime()` is false, and the interpreter bridge only backs
the non-array forms in a no-`vulkan` build.

## Fix options (owner decision)

1. Build the seed with the runtime `vulkan` feature on macOS (MoltenVK), so JIT
   calls the real runtime implementation; then land the arena widening.
2. Or make the interpreter bridge back the 11 `_array` symbols, then land the
   splice predicate and the arena widening together.

Either way the acceptance is: `vk_probe` reports `backend=vulkan` under JIT, and
the 320x240 capture is byte-identical (`cmp`) to the interpreted capture.

## Repro

```
# SEED = a seed built from origin/main (cargo build --release --bin simple)
SIMPLE_GPU_BACKEND=vulkan SIMPLE_SHOWCASE_FRAMES=1 \
  "$SEED" run src/app/ui_showcase/hosts/main_2d_gpu.spl 2>&1 | grep -E 'PANIC|engine-demotion'
```
