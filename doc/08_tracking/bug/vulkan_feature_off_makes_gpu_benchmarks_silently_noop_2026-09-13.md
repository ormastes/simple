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

## 2026-11-07 current-owner audit — do not gate the wrong backend family

The original implementation inventory above is historical. At authenticated
release/1.0.0 `68a6f89671421a65a1b99faba1b76cba592850eb`, `gpu.rs`
contains two distinct Vulkan families. The `rt_vk_*` runtime wrappers are
conditional on the Cargo `vulkan` feature. The interpreter's `rt_vulkan_*`
family instead owns an unconditional dynamic-loader implementation.

`interpreter_extern/mod.rs` registers `rt_vulkan_is_available`,
`rt_vulkan_alloc_buffer`, `rt_vulkan_dispatch` and
`rt_vulkan_submit_and_wait` directly to that second family. Its buffer
handler calls the loaded `create_buffer` pointer and its dispatch handler
calls the loaded `cmd_dispatch` pointer; they do not become the feature-off
`rt_vk_*` stubs. Source identities are `gpu.rs` Git blob
`82acf26bdd90ce5eb973efead9148087637546c1` and registration-module blob
`552f1cc72ed6f302cbb27a68b2a039921ffc902b`.

Consequently, adding `cfg!(feature = "vulkan")` to the existing interpreter
availability handler would hide an implemented default-build backend. An
isolated proposal doing that was rejected by independent source review and
withdrawn before publication or execution. No availability predicate,
feature selection, runtime symbol, loader, dispatcher or device state was
changed. Do not repeat that proposed fix based only on Cargo forwarding or
the older family inventory.

Disposition: current interpreter source no longer matches the stated
feature-off/stub mechanism. This is source evidence, not a device or benchmark
PASS. Default-build execution, native/JIT routing and real transfer/dispatch
must be bound to their actual selected provider before declaring the whole
record resolved. No GPU, performance or platform checks were run in this
audit, and the canonical BugDB row remains untouched and OPEN.
