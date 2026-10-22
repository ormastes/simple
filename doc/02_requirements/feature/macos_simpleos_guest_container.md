# macOS host for SimpleOS containers

**Superseded 2026-09-27:** The user corrected the execution model: Simple
Container is not a VM. Mac programs run on macOS; SimpleOS programs run on
SimpleOS. The selected requirements are in
[native_macos_simple_container.md](native_macos_simple_container.md). The VM
requirements below are historical and are not acceptance criteria.

Selected from the user's direction on 2026-09-26: reuse the SimpleOS container
logic and make it usable from macOS. The execution OS is SimpleOS; the physical
host is macOS. This is a VM runtime class, not a Darwin native container or a
claim that SimpleOS can execute arbitrary Linux OCI images.

| ID | Requirement | Acceptance |
|---|---|---|
| REQ-MSG-001 | A macOS host boots a verified SimpleOS image using an admitted QEMU/HVF launch plan. | Fresh VM boot identity and verified image digest are recorded. |
| REQ-MSG-002 | A bounded host request reaches a guest dispatcher that invokes the existing `SimpleOsContainerProviderV1` with real kernel scheduler/context authority. | The returned task ID is bound to the same attempt, guest boot, image, and policy. |
| REQ-MSG-003 | Host result publication requires the guest provider's observed kernel task exit and matching attempt nonce. | Mismatch, timeout, VM exit, or missing kernel exit yields `BLOCKED`; no success receipt. |
| REQ-MSG-004 | Pod/Job placement identifies physical host macOS, execution OS SimpleOS, and `virtual-machine` runtime class. | No `native-container` fallback and no cross-OS image substitution. |

Current state: the pure attempt/observation value boundary for REQ-MSG-002/003
exists. None of these four acceptance rows has a live macOS VM PASS yet.
