# `VulkanFfi.loader_probe()` reports false on a host with a working Vulkan loader

**Filed:** 2026-08-09 (stream F4)
**Subject:** `src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl`, `loader_probe()`
**Host:** Linux x86_64, `libvulkan.so.1 -> libvulkan.so.1.3.275`

## Summary

`loader_probe()` is documented as the raw signal *"does the dynamically
loaded library resolve the real `vkEnumerateInstanceVersion` export? True
here means 'a Vulkan loader is present'"*.

On this host a Vulkan loader **is** present and does export that symbol:

```
$ nm -D --defined-only /usr/lib/x86_64-linux-gnu/libvulkan.so.1 \
    | grep -c vkEnumerateInstanceVersion
1
```

`create_dynamic()` successfully dlopens it (returns non-nil). Yet:

```
loader_probe=false
```

## Cause

```
fn loader_probe() -> bool:
    match self._mode:
        case Static: false
        case Dynamic:
            if self._dyn_lib != nil:
                val result = self._dyn_lib.call0("vkEnumerateInstanceVersion")
                result != 0
```

`vkEnumerateInstanceVersion` returns a `VkResult`, and `VK_SUCCESS` is
**0**. The predicate `result != 0` therefore treats a *successful* call as
"loader absent". The test is inverted with respect to the value it reads.

## The deeper problem: the probe cannot distinguish its two outcomes

Inverting the comparison is not a sufficient fix. `call0` on an
**unresolved** symbol also yields 0 in this FFI. So both
"resolved and succeeded" and "not resolved at all" produce 0, and the
proposed `result == 0` would report true in both cases — a probe that
always says "loader present".

`vkEnumerateInstanceVersion(uint32_t *pApiVersion)` additionally takes an
out pointer that `call0` does not supply, so even a correct status read is
being obtained by calling the function with a garbage/absent argument.

A correct implementation needs a resolution check that is distinct from the
call's return value — i.e. a `dlsym`-succeeded signal (a `DynLib.has_symbol`
/ `DynLib.sym` returning a nullable address), not a status-code comparison.
That primitive does not appear to exist on `DynLib` today; adding it is
probably part of this fix.

## Impact

Low severity in isolation — `loader_probe()` is documented as a raw
diagnostic and `is_available()` (the real capability gate) is correctly
false in Dynamic mode regardless. But it is a capability signal that is
wrong in the direction of under-reporting, and its docstring promises
something it cannot currently deliver.

## Spec status

`test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl` asserts
`loader_probe() == false` **only for Static mode**, where false is correct
by construction. It deliberately does not assert the Dynamic-mode value in
either direction, because both the current `false` and a naively "fixed"
`true` would be asserting an unreliable signal. Once `DynLib` gains a real
symbol-resolution check, add a Dynamic-mode case.

## Reproduce

```bash
cat > probe.spl <<'EOF'
use std.nogc_sync_mut.gpu.engine2d.ffi_vulkan.{VulkanFfi}
fn main():
    val v = VulkanFfi.create_dynamic()
    if v == nil:
        print("NIL"); return
    print("loader_probe=" + v.loader_probe().to_text())
EOF
SIMPLE_MODULE_LIMIT=4000 bin/simple run probe.spl
```
