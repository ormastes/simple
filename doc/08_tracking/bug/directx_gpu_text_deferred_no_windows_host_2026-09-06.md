# DirectX has no GPU text on either platform; deferred for want of a Windows D3D11 host

Date: 2026-09-06
Status: DEFERRED (no Windows host; Linux lane is a counter-handle fake) —
re-verified unchanged 2026-11-11 (lane ne6); the triage host IS Windows, but no
device-verifiable text path exists to exercise, so the deferral stands (see
addendum)
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

---

## Addendum 2026-11-11 (lane ne6, batch p3-ne6)

**Verdict: DEFERRED stands, source-verified unchanged.** Re-read at tip on
branch work/p3-ne6-20261111:

- `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl` `draw_text_bg`
  (:229-231) and `draw_text` (:390-392) still hand both calls to the software
  mirror and then `_poison_native_receipt()` — the honest-poison shape this
  doc describes is intact, and no GPU text lane has been added.
- `src/lib/common/gpu/font_atlas_composite.spl` still has no HLSL twin;
  `src/runtime/runtime_directx_core.c` still exports no compute/present
  entries for text.
- The `# TODO(P2,gpu)` markers this doc says stay TODOs are still TODOs
  (`backend_directx.spl:49`).

Host-limit note: this triage runs on a Windows host, which satisfies the
letter of "a Windows host" but not the closing evidence: there is still no
real D3D11 text path to compile and run — the `_WIN32` C branch provides
device open/execute-readback only. Building the text lane remains the deferred
work, and a device-verified text frame remains the unmet closing condition.
No scope decision ("DirectX text is out of scope") has been written down, so
the record stays open per its own rule.
