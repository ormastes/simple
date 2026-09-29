# DirectX has no GPU text on either platform; deferred for want of a Windows D3D11 host

Date: 2026-09-06
Status: DEFERRED (no Windows host; Linux lane is a counter-handle fake)
Area: lib / gc_async_mut / gpu / engine2d — DirectX backend

All `file:line` below were read at `origin/main` `461e48379ff` (2026-09-06).

## Symptom

`DirectXBackend` renders **no** text on the GPU, on **either** platform. Both
text entry points hand the call to the software backend and then explicitly
poison the native receipt so no device claim can be made:

```
src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl:221-223
    me draw_text_bg(x, y, text_val, fg, bg, font_size):
        self.sw.draw_text_bg(x, y, text_val, fg, bg, font_size)
        self._poison_native_receipt()

src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl:382-384
    me draw_text(x, y, text_val, color, font_size):
        self.sw.draw_text(x, y, text_val, color, font_size)
        self._poison_native_receipt()
```

This is honest and self-labelled — the poison is the mechanism that stops the
CPU pixels from being stamped as device output. The gap is that there is no GPU
text lane at all, not that an existing one lies.

## Why it is deferred rather than built

**1. The Windows path cannot be built or run on this host.** The real D3D11
code is C, guarded by `#if defined(_WIN32)` (`src/runtime/runtime_directx_core.c`),
with `ClearRenderTargetView` / `CopyResource` / `Map(..., D3D11_MAP_READ)` behind
that guard. This is a macOS reference machine; the `#else` branch returns 0
honestly. Nothing about a Windows text lane can be exercised, let alone verified,
from here.

**2. The Linux DXVK path is a counter-handle fake, so a text lane on it would be
fake by construction.** `src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl:204,218`
states it in its own docstring — queue submit and present are "pending rt_dlopen
for real libvulkan"; handles are `count + 1` counters and no device is touched.
`dxvk_d3d11.spl` does its upload/readback with an in-Simple pixel copy. Adding
`draw_text` there would produce CPU pixels behind a device-shaped handle — the
exact false-evidence shape PR #410 (OPEN as of 2026-09-06) removed from
`backend_directx.spl:444,452`, where CPU-rasterized pixels were returned with
`source = "device_readback"` and a positive handle, and a spec *pinned* the fake.

Building GPU text on either half would therefore either be unbuildable or
dishonest. Neither is an acceptable outcome, so the gap is recorded.

The existing `# TODO: [gpu]` markers for this gap **stay TODOs**.

## Closing evidence (what flips Status)

Either of:

- **A Windows host with a real D3D11 text path**: the `_WIN32` branch compiled
  and run on Windows, a device-produced text frame read back through
  `Map(..., D3D11_MAP_READ)`, `native_receipt_eligible` genuinely true (no
  `_poison_native_receipt()` on the text path), and a pixel diff against the
  software rasterizer — recorded with the host identity and a capture; **or**
- **an explicit scope decision that DirectX text is out of scope**, written down
  here, after which `draw_text`/`draw_text_bg` keep the software + poison shape
  permanently and this record closes as WONTFIX rather than sitting open forever.

A green run of `backend_directx_spec.spl` on this host is **not** closing
evidence: its Linux `init()` reduces to an `rt_file_exists` probe for
`libvulkan.so` (`nogc_async_mut/gpu/vulkan_icd_sffi.spl`), so it is device-free by construction.
