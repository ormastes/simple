# All four `gc_async_mut` GPU engine2d FFI facades are dangling re-exports

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Filed:** 2026-08-09 (stream F4)
**Severity:** high — the modules are unusable, and the breakage is silent
**Found while:** replacing the tautology-shell specs recorded in
`gated_specs_are_tautology_shells_2026-08-09.md`

## Summary

Each of these four files is a 3-line facade whose sole `export use` names a
module that **does not exist on disk**:

| facade | re-export target | target exists? |
|---|---|---|
| `src/lib/gc_async_mut/gpu/engine2d/ffi_cuda.spl` | `std.nogc_async_mut.gpu.engine2d.ffi_cuda` | **NO** |
| `src/lib/gc_async_mut/gpu/engine2d/ffi_vulkan.spl` | `std.nogc_async_mut.gpu.engine2d.ffi_vulkan` | **NO** |
| `src/lib/gc_async_mut/gpu/engine2d/ffi_intel.spl` | `std.nogc_async_mut.gpu.engine2d.ffi_intel` | **NO** |
| `src/lib/gc_async_mut/gpu/engine2d/ffi_rocm.spl` | `std.nogc_async_mut.gpu.engine2d.ffi_rocm` | **NO** |

`src/lib/nogc_async_mut/gpu/engine2d/` contains only `sffi_cuda.spl`,
`sffi_intel.spl`, `sffi_opencl.spl`, `sffi_rocm.spl`, `sffi_vulkan.spl` —
the `s`-prefixed SFFI variants. There is no `ffi_*.spl` there at all. The
real `CudaFfi` / `VulkanFfi` / `IntelFfi` / `RocmFfi` classes live in
**`src/lib/nogc_sync_mut/gpu/engine2d/ffi_*.spl`**, a different tier.

This is the whole family — all four facades in the directory are broken the
same way. By contrast `src/lib/gc_async_mut/gpu/device.spl` resolves fine
(it points at `std.common.gpu.device` and `std.nogc_sync_mut.gpu.device`),
so this is specific to the `engine2d/ffi_*` set.

## Why it stayed invisible

An unresolved `use` is only a **warning**, never an error. The single
diagnostic emitted is about style, not resolution:

```
warning: Avoid 'export use *' - exposes unnecessary interfaces
  --> src/lib/gc_async_mut/gpu/engine2d/ffi_cuda.spl:3:1
```

Nothing says the target is missing. The failure only appears at the call
site, at runtime, as an unresolved symbol.

## Reproduce

```bash
cat > probe.spl <<'EOF'
use std.gc_async_mut.gpu.engine2d.ffi_cuda.{CudaFfi}
fn main():
    val f = CudaFfi.create_static()
    print(f.api_name())
EOF
SIMPLE_MODULE_LIMIT=4000 bin/simple run probe.spl
```

Verbatim result:

```
Runtime error: Function 'create_static' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap,
not a program error. Refusing to substitute a placeholder value ...
```

Note the process still **exits 0**, so a caller that ignores stderr sees a
success.

Swapping the import to `std.nogc_sync_mut.gpu.engine2d.ffi_cuda` works:

```
api_name=CUDA Driver API
```

## Impact

Four spec files claimed `@cover <facade> 80%`. A facade that exports nothing
cannot be 80% covered by anything; the coverage figures for these modules
are meaningless. Stream F4 repointed the `ffi_cuda` and `ffi_vulkan` specs at
the real `nogc_sync_mut` modules; `ffi_intel` and `ffi_rocm` were downgraded
to an honest no-coverage claim pending this fix.

## Fix options (not done here — F4 is forbidden from fixing product code)

1. Point each facade at `std.nogc_sync_mut.gpu.engine2d.ffi_<name>` (matches
   where the classes actually are, and matches what `gpu/device.spl` does).
2. Or delete the four facades if the `gc_async_mut` tier is not meant to
   re-export them, and fix any importer.

Option 1 is the smaller change and is consistent with the sibling
`device.spl` facade. **Do not** pick a facade target without checking which
tier the class actually lives in — the `sffi_*` files next door are a
different mechanism, not a drop-in.

## Follow-up worth doing separately

An unresolved `use` / `export use` target should be an **error**, not a
warning. This defect class is invisible precisely because it is not. See the
existing note `reference_unresolved_use_is_only_a_warning_so_delete_verification_is_fail_open`.
