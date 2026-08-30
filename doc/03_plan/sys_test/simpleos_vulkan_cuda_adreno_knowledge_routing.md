# System Test Plan: SimpleOS GPU and Knowledge Routing

| Requirement | Evidence |
|---|---|
| REQ-001..003 | Processing/Vulkan port unit tests and QEMU typed receipt scenario |
| REQ-004..005 | Adreno readiness/provenance tests and native board blocker row |
| REQ-006..009 | deterministic knowledge routing unit/integration scenario |
| REQ-010 | environment matrix with exact resume metadata |
| NFR-001..002 | device-origin, identity, handle, correlation, backend/class rejection |
| NFR-003 | owned decision inventory: 162/164 outcomes = 98% |
| NFR-004..005 | probe-cache and invalidation tests |
| NFR-006 | repeatable receipt/hash ordering test across input permutations |
| NFR-007..008 | environment, stub, facade, duplication, and file-size gates |
| NFR-009 | Venus admission/wire tests remain device-free and the environment row stays blocked without live controlq submission/fence/readback proof |

The staged Venus protocol test lane is split deliberately:

- device-free admission tests validate feature/capset bounds, identifiers,
  prerequisite ordering, and fail-closed planning;
- eight device-free wire scenarios validate exact packed little-endian request
  bytes plus typed response/type/flag/fence rejection; their current 8/8 pass
  is provisional pending a pure-Simple self-hosted runner;
- the native QEMU environment row alone validates the guest ICD, shared memory,
  real virtqueue submission, correlated completion, and device-origin readback.

A green device-free lane must not change the direct guest-native environment
row from blocked to passing.

The kernel BAR-window unit lane covers all six tracked binary decisions (12 of
12 outcomes): BDF presence/cardinality, BAR index/row cardinality, memory kind,
assigned nonzero aperture, checked containment, and physical-addition overflow.
It includes BAR0/BAR5, a 64-bit BAR above 4 GiB, exact-final-byte admission,
one-byte escape, offset-underflow defense, duplicate rows, and exact provenance.
This proves policy only; syscall, VMA, unmap, fork, and live PCI tests remain.

The device-memory ownership lane adds ten tracked outcomes: device versus
PMM-owned leaf release, device-VMA present/absent, fork allowed/denied, resource
kind inheritable/non-inheritable, and all-resource-set allowed/denied. Fixtures
cover empty/ordinary VMAs, inconsistent live counts, device slots at every
position, anonymous/file/shared kinds, notification/IRQ resources, DMA/BAR at
either position, and unknown future resources. Integration evidence still must
prove USER|UC|NX PTEs, collision rejection, partial-map rollback, no PMM delta,
fork/exec `EBUSY`, explicit release restoring fork, and teardown ordering.

The new explicit transaction integration fixture covers unaligned physical
envelopes, exact PTE physical/USER/UC/NX flags, stale-PTE preservation, injected
middle-map rollback, exact-provenance/extent unmap, PMM invariance, and identical
virtual addresses in two isolated process spaces. The planner passes 14/14.
The transaction fixture currently reaches PMM initialization but the bootstrap
runner then reports `no examples executed`; the unchanged
`memory_leveling_vmm_effects_spec.spl` reproduces that environment failure.
Keep this row blocked and rerun both with the rebuilt pure-Simple runner before
claiming integration or release evidence.

The implemented bounded integration lane is `virtio_gpu_venus_controlq`; its
device-free admission and source-boundary contract is followed by the remaining
live queue work: explicit descriptor ownership, distinct queue-full/timeout
results, reset-generation invalidation, used-length validation, and retained
device-written response evidence. It must
not claim native Vulkan until a Venus-capable environment also proves ICD,
mapping, submission, completion, and readback.

Native UNO Q command and artifact paths must be supplied by the board wrapper;
until then its executable scenario fails closed rather than skips.
