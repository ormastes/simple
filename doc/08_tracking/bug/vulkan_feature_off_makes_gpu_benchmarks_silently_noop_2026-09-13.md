# `rt_vulkan_is_available()` returns true while the whole compute path is a stub

- **Status:** open — the false advertisement is unfixed; the workaround is known
- **Severity:** high for anyone trying to measure GPU performance
- **Found:** 2026-09-13, after repeated failed attempts to obtain a Vulkan
  frame-time number

## The trap

`src/compiler_rust/compiler/Cargo.toml` has `default = []`, so a normal
`cargo build --release --bin simple` produces a seed **without** the `vulkan`
feature. In that build:

- `rt_vulkan_init`, `rt_vulkan_device_count`, `rt_vulkan_select_device` and
  `rt_vulkan_is_available` **work**, because `interpreter_extern/gpu.rs`
  implements them over its own `vulkan_dlopen` (ash loaded dynamically),
  independent of the cargo feature;
- `rt_vulkan_alloc_buffer`, `rt_vulkan_copy_to_buffer_array`,
  `rt_vulkan_dispatch`, `rt_vulkan_submit_and_wait` and the rest of the
  buffer/compute surface delegate to
  `simple_runtime::vulkan_graphics_runtime::*`, which is `#[cfg(feature =
  "vulkan")]`. Without the feature they compile to the
  `#[cfg(not(feature = "vulkan"))]` stubs that `return 0`.

So the probe says Vulkan is present and usable, the device enumerates, a buffer
handle comes back — and every actual transfer or dispatch silently fails. A
benchmark written against that surface reports nothing and exits 0.

This is what `test/05_perf/graphics_2d/bench_2d_vulkan.spl` was doing: it
printed its banner and stopped, with no error, on a host where Vulkan is fully
functional.

## The workaround, verified

```
cargo build --release --bin simple --features vulkan
```

Pulls `ash`, `gpu-allocator`, `spirv-reflect`, `ash-window`, `winit`,
`raw-window-handle`. Builds clean on this Windows host in ~7 minutes. With that
binary the benchmark runs end to end:

```
Vulkan device count: 1
Device FB: 8294400 bytes, handle=1
Shaders compiled OK.  Pipelines created OK.  Descriptor sets bound OK.
Timed: 100 frames...
BENCH_RESULT scene=fill_1080p backend=vulkan_compute frames=100 avg_us=7588 rects_per_frame=100 fb=1920x1080
```

Four samples on this host: **7588, 8117, 10324, 7380 us/frame** — median ~7.9
ms, ~39% spread, which is what a shared desktop under load looks like. Any
before/after GPU comparison on this machine needs enough samples to see past
that, not two runs.

## The actual defect

`rt_vulkan_is_available()` answers a question nobody asked. It reports whether
the **loader** can be dlopened, not whether this binary can **do** anything with
Vulkan. Those differ exactly when the feature is off, which is the default
build. A capability probe that returns true for a build whose compute path is
stubbed is a false advertisement, and it converts every downstream failure into
a silent one.

Two candidate fixes, neither applied here:

1. Make `rt_vulkan_is_available` (or a new `rt_vulkan_compute_available`)
   return false when the feature is absent, so callers can branch honestly.
   This is the smaller change and matches what every caller actually means.
2. Stop gating the buffer/compute surface differently from the probe surface,
   so a build either has Vulkan or does not.

Until one lands, `scripts/check/check-vulkan-compute-real.shs` detects the
mismatch on a built binary rather than letting a benchmark discover it by
producing nothing.

## Cost

This cost most of a session. The failure mode is maximally misleading: the probe
is green, the device is real, the handle is non-zero, and the only symptom is a
benchmark that prints its header and exits 0 — which reads as "the benchmark is
broken" rather than "this binary cannot do Vulkan".
