# System Test Plan: SimpleOS GPU and Knowledge Routing

| Requirement | Evidence |
|---|---|
| REQ-001..003 | Processing/Vulkan port unit tests and QEMU typed receipt scenario |
| REQ-004..005 | Adreno readiness/provenance tests and native board blocker row |
| REQ-006..009 | deterministic knowledge routing unit/integration scenario |
| REQ-010 | environment matrix with exact resume metadata |
| NFR-001..002 | device-origin, identity, handle, correlation, backend/class rejection |
| NFR-003 | owned decision inventory: 40/42 outcomes = 95% |
| NFR-004..005 | probe-cache and invalidation tests |
| NFR-006 | repeatable receipt/hash ordering test across input permutations |
| NFR-007..008 | environment, stub, facade, duplication, and file-size gates |
| NFR-009 | Venus protocol-admission tests remain structural-only and the environment row stays blocked without submission/fence/readback proof |

The staged Venus protocol test lane is split deliberately:

- device-free tests validate feature/capset admission, bounds, identifiers,
  prerequisite ordering, and reset invalidation;
- the native QEMU environment row alone validates the guest ICD, shared memory,
  real virtqueue submission, correlated completion, and device-origin readback.

A green device-free lane must not change the direct guest-native environment
row from blocked to passing.

Native UNO Q command and artifact paths must be supplied by the board wrapper;
until then its executable scenario fails closed rather than skips.
