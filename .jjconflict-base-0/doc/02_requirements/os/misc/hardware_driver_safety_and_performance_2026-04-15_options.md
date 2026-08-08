<!-- codex-research -->
# Hardware Driver Safety And Performance Feature Options

## Option A: Safety-first VirtIO hardening

Description:
Harden `virtio_blk` and `virtio_net` first by removing unsafe DMA assumptions, then add completion-mode selection and zero-copy hooks.

Pros:
- Highest immediate correctness payoff
- Reuses existing VirtIO code paths already exercised in QEMU
- Low architecture churn

Cons:
- Does not immediately add new hardware breadth
- GPU and RDMA remain incomplete after the first phase

Effort:
M (4-7 files)

## Option B: Balanced hardening plus NVMe queue validation

Description:
Do Option A, then add queue-invariant checks and diagnostics to NVMe before touching new hardware families.

Pros:
- Improves both storage stacks
- Strengthens DMA/completion correctness across two driver families

Cons:
- Slightly larger patch train
- Still does not introduce new NIC or RDMA features

Effort:
L (7-11 files)

## Option C: Broad hardware expansion

Description:
Pursue VirtIO hardening, GPU completion, plain NIC work, and RDMA groundwork in one stream.

Pros:
- Expands supported surface fastest
- Produces a visible roadmap across all hardware topics

Cons:
- Highest risk of mixed unstable work
- Hardest to verify safely
- Likely to produce partial rather than finished lanes

Effort:
XL (12+ files)
