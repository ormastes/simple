# Supplemental parallel lanes: SimpleOS pure-Simple Venus protocol

This supplements the canonical file-ownership plan at
`doc/03_plan/agent_tasks/simpleos_venus_gpu_stack.md`.  Its interface names,
helper names, merge owner (`/root`), and final highest-capability review are
binding; this document does not create alternate contracts.

| Parallel lane | Canonical non-overlapping scope | Acceptance focus |
|---|---|---|
| A | `virtio_gpu_discovery.spl`, `virtio_gpu_regs.spl`, focused unit specs | cap visits ≤48, DEVICE_CFG, SHM id 1, BAR arithmetic/containment |
| B | `virtio_gpu_capset.spl`, `virtio_gpu_init.spl`, focused specs | capsets ≤64, payload ≤4072, complete/partial tuples, no id-only pass |
| C | `_Venus/protocol.spl`, then `blob.spl`/`ring.spl` | upstream-generated handshake, host-visible blob, guest-authored ring |
| D | `_Venus/queue.spl`, `fence.spl`, `readback.spl` | three in-flight max, correctly indexed fence, provenance-carrying readback |
| E | existing compositor backend and QEMU system wrapper/spec/manual | receipt-gated selection, exact pixels/checksum, `qemu_only`, no CPU fallback |

Dependency order is A/B → C → D → E, but A and B are independent once the
frozen receipt types land.  Lanes C–E retain explicit fail-fast tests until
their lower layer is implemented; no agent may convert an unavailable fixture
into a pass.
