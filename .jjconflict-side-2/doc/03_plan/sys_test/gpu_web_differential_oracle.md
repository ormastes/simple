# GPU/Web Differential Oracle Test Plan

| Scenario | Layer | Oracle |
|---|---|---|
| mapped candidate/reference handles | all | semantic comparison matches only under explicit ID map |
| capability/capset mutation | virtio/Venus | changed scalar fact is rejected |
| submit/barrier/fence mutation | Vulkan | order/result/error divergence is rejected |
| pixel digest mutation | Draw IR/Vulkan/Web paint | exact final observation is rejected |
| missing device-origin readback | live GPU profile | profile blocks promotion |
| display-list/layerization transformation | web | semantic projection matches without byte equality |
| missing library/symbol/ABI error | dynamic oracle | bounded error and unavailable status, never a synthetic pass |
| malformed/reordered/oversized trace | shared | schema/profile rejects it |
| incomplete/dropped trace | shared | comparison is ineligible before oracle evaluation |
| wrong UI/arch/transport/features/Venus/device/oracle/fallback | GPU profile | exact profile fact rejection |

Performance tests record adapter load time once, per-fixture normalization time,
trace event count, p50/p95 readback time, and maximum RSS. No live test passes
on CPU fallback, synthetic Chrome output, or an unreviewed golden.
