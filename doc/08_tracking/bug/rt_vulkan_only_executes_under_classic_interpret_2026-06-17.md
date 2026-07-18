# rt_vulkan_* Only Execute Under Classic Interpreter - 2026-06-17

## Severity
P1 — GPU backends silently no-op (report zero devices) outside the classic
interpreter, with no error surfaced. This is the substrate that makes
GPU-backend provenance unreliable across execution modes.

## Component
- Real impl: `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`
  (`vulkan_dlopen` module, `rt_vulkan_init_fn`, `rt_vulkan_dispatch_fn`, ...)
- Native stub: `src/runtime/runtime_native.c:147`
  `int64_t rt_vulkan_device_count(void) { return 0; }`
- JIT/AOT symbol table: `src/compiler_rust/compiler/src/elf_utils.rs` (does NOT
  list `rt_vulkan_init`; lists only the C-stub `rt_vulkan_device_count`).

## Summary
A single small probe (`rt_vulkan_init()` + `rt_vulkan_device_count()`) returns
different results purely as a function of the execution mode, with no diagnostic:

| Execution mode | `rt_vulkan_init` | `rt_vulkan_device_count` |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` (classic) | 1 | 3 (TITAN RTX, A6000, llvmpipe) |
| `SIMPLE_EXECUTION_MODE=interpret-optimized` | 0 | 0 |
| default `bin/simple run` (JIT) | 0 | 0 |

The host has real Vulkan (libvulkan 1.3.275, NVIDIA + Mesa lavapipe ICDs);
`vulkaninfo` enumerates 3 devices. Only the classic interpreter sees them.

`bin/simple test` (spec harness) runs specs in the **classic interpreter**, so
real `rt_vulkan_*` *do* execute under `bin/simple test` — but the same code via
`bin/simple run` (JIT) or `interpret-optimized` silently gets zero devices.

## Root Cause
- The genuine Vulkan implementation lives only in the interpreter extern
  (`gpu.rs`), via a `dlopen("libvulkan.so.1")` path that calls real
  `vkCreateInstance` / `vkEnumeratePhysicalDevices` / `vkCmdDispatch` etc.
- The JIT/AOT path resolves `rt_vulkan_device_count` to the native C stub in
  `runtime_native.c` (hardcoded `return 0`), and does not link the real impl.
- The optimized interpreter path does not register the real `rt_vulkan_*`
  externs, so they resolve to nothing usable → 0.

No fallback warning or error is emitted in the 0-device modes; callers that ask
for a GPU backend just silently get nothing and (per the related web-render bug)
may still stamp GPU provenance.

## Reproduce
```
cat > /tmp/vk_probe.spl <<'EOF'
extern fn rt_vulkan_init() -> i64
extern fn rt_vulkan_device_count() -> i64
fn main():
    print(rt_vulkan_init().to_text()); print(" ")
    print(rt_vulkan_device_count().to_text()); print("\n")
EOF
bin/simple run /tmp/vk_probe.spl                              # -> 0 0  (JIT, C stub)
SIMPLE_EXECUTION_MODE=interpret bin/simple run /tmp/vk_probe.spl   # -> 1 3  (real Vulkan)
SIMPLE_EXECUTION_MODE=interpret-optimized bin/simple run /tmp/vk_probe.spl  # -> 0 0
```

## Proposed Fix (separate change — not applied here)
- Either implement the real Vulkan path in the native runtime (replace the
  `runtime_native.c` stubs with a `dlopen`-based impl mirroring `gpu.rs`), or
- Register the real `rt_vulkan_*` externs in the optimized interpreter and the
  JIT symbol table so all execution modes agree, or
- At minimum, emit a one-time diagnostic when a GPU backend is requested but the
  active execution mode cannot provide a real device, so callers stop silently
  treating "0 devices" as "rendered on GPU".

## Related
- `web_render_gpu_backend_provenance_fabricated_2026-06-17.md`
