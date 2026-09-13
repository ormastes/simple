# Deterministic Feature and Layer Knowledge Selection

Before implementation, resolve the exact feature ID in
`doc/00_llm_process/knowledge_registry.sdn`, then longest-prefix match every
planned or changed `src/**` path. Load the feature-group base and exact feature
expert, plus every matched layer-base and layer expert. Deduplicate and order
paths lexically so all pair-programming participants use the same bundle.

Missing feature IDs, missing layer routes, equal-length competing prefixes, and
empty path lists fail closed. Record registry version, feature, selected paths,
source-to-prefix decisions, and architecture profiles in
`.spipe/<feature>/knowledge_selection.sdn`. Implementation and verification
consume that receipt; they do not reconstruct selection heuristically.

The Simple selector is `std.common.llm.knowledge_selector`. Paths under
`src/os/kernel/**` and `src/os/drivers/**` are always `mdsoc_only`; a registry
entry attempting MDSOC+ there is rejected. Userland services/apps may select
`mdsoc_plus`. Private wiki material may attach by stable ID but cannot replace
the public registry or weaken architecture policy.

## Rendering and UI optimization route

Use the exact feature route for `simple_2d_web_renderer_gpu_optimization`,
`web_renderer_vulkan_4k_showcase_hardening`, or
`chromium_web_renderer_primitive_differential`. For renderer source changes,
the longest-prefix routes for
`src/lib/gc_async_mut/gpu/engine2d` and
`src/lib/gc_async_mut/gpu/browser_engine` select the `rendering_ui` group and
the `gpu_offload_check` expert.

The selected bundle requires explicit residency and async evidence:
device-local allocation versus persistently mapped staging bytes, transfer or
graphics queue ownership, nonblocking fence/timeline completion, bounded frame
ring, and generation-tagged damage scheduled from coalesced events. Timed
display is readback-free; exact RGBA capture is a separate post-timing action.
Unknown counters and CPU fallback are not zero and cannot be admitted.

For parity, C Vulkan and Simple Vulkan must share the fixture, event script,
viewport, format, warmup/sample schedule, timing boundary, and device/queue
identity. Simple Web versus Chrome also needs a matching semantic trace and a
device-origin receipt. Missing canonical Chrome library/runner is an explicit
non-admission, not a reason to publish a ratio from a fixture or diagnostic
dylib.
