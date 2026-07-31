# Layout Framework Non-Functional Requirements

The selected NFR scope is derived from the plan's acceptance gates.

- NFR-001 Determinism: identical snapshots and profiles produce identical islands, waves, geometry, mappings, and receipt hashes.
- NFR-002 Termination: fixed-point scheduling has a finite configurable cap greater than zero and never loops without a verdict.
- NFR-003 Correctness: CPU geometry is the absolute oracle; incremental and accelerated boxes/fragments/line boxes/overflow require structural equality before acceptance.
- NFR-004 Cost honesty: every island has a recorded CPU/GPU estimate including scheduling, host/device transfer, readback, and synchronization; estimates never masquerade as execution.
- NFR-005 Text fidelity: shaping is obtained only through TextMeasurePort; unavailable shaping fails closed to CPU.
- NFR-006 Incrementality: clean islands are not visited and every visited island is named in evidence.
- NFR-007 Isolation: common framework code adds no raw runtime, browser-backend, font-cache, atlas, or device ownership.
- NFR-008 Maintainability: shared contracts stay in owner modules; CPU and GPU algorithms enter through execution ports, and the framework does not duplicate the current browser layout algorithms.
