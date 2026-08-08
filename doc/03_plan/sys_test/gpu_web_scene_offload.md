# GPU Web Scene Offload System Test Plan

Scope: packet/receipt correlation, single owner, stale rejection, explicit CPU
fallback, and projection ownership. Excluded until a backend lands: claims of
Vulkan/WebGPU device execution, QEMU pixels, and full WM GPU ownership.

Run focused unit/spec checks with the deployed pure-Simple runtime, then
generate the mirrored manual with `spipe-docgen`. A passing source oracle does
not promote native GPU execution.

| Requirement | Evidence | Coverage |
|---|---|---|
| REQ-001 | existing `gpu_event_core_spec.spl`; boundary spec ordered input scenario | full contract |
| REQ-002 | `simple2d_gpu_event_boundary_spec.spl` exact receipt and mismatch cases | full contract |
| REQ-003 | same spec unavailable, timeout, stale, and invalid-marker cases | full contract |
| REQ-004 | architecture/design plus future production integration spec | partial |
| REQ-005 | explicit promotion gate; backend/QEMU evidence absent | correctly postponed |

Pass: all executable assertions pass, docgen reports zero stubs, and no `.spl`
exists under `doc/06_spec`. Fail: telemetry accepted as device execution, two
owners, unnamed fallback, stale replay, or unsupported privileged GPU effect.

