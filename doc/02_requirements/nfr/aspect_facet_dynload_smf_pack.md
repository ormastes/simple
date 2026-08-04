# Aspect Facets and Demand-Loaded SFM Packs — NFR Requirements

## Requirements

- **NFR-AF-001 — Determinism.** Identical sources, lockfile, toolchain, target, resolved variants, and aspect profile produce byte-identical logical catalogs, binding order, and pack indexes. Catalog/cache keys include pack digest, module digest, target, resolved variant fingerprint, runtime ABI, and relevant core public/layout ABI.
- **NFR-AF-002 — Cold-path isolation.** For catalogued `manual` or `lazy_facet` aspects before activation: zero aspect-pack opens, zero aspect-payload bytes read/decompressed, zero aspect executable mappings, zero sidecar allocations, and zero runtime directory/config scans. Existing non-aspect dynSMF startup behavior is outside this claim.
- **NFR-AF-003 — Exact overhead claims.** A facet-only business path contains no aspect branch. A statically omitted aspect may claim byte-identical output only when verified. Patchable dynamic advice must report and measure its disabled code/branch footprint and must never be described as exact zero overhead.
- **NFR-AF-004 — Bounded resource behavior.** Pack/index/module caches define size limits, decoded-size limits, eviction/refcount policy, invalidation by catalog/generation/digest, and bounded negative caching. Subprocess capture, when used, follows the shared 4 MiB-per-stream facade contract.
- **NFR-AF-005 — Startup and lookup evidence.** Checked-in baselines measure startup wall time/RSS/page faults, first-use p50/p95/p99, repeated facet lookup cost, opened files, bytes read/decompressed, and cache hit/miss/eviction counts on representative fixtures. Thresholds are derived from baselines rather than invented.
- **NFR-AF-006 — Security and mission-critical profile.** Signed/digested exact artifacts, W^X, capability limits, no lazy I/O after operational transition, deterministic ordering, and fault injection are fail-closed. Dynamic attach/unload/patching are denied by the mission-critical default profile.
- **NFR-AF-007 — Architecture and facade compliance.** Shared IDs/contracts obey MDSOC next-layer/common-node ownership; app/feature leaves use existing file/env/process facades and add no local raw `rt_*` shortcuts.
- **NFR-AF-008 — Compatibility.** Existing ordinary SMF v0.1 readers/writers, compile-time AOP behavior, dynSMF disable controls, and manifest-derived evidence remain compatible. The aspect-pack format evolves SFM, not SMF.

## Verification mechanisms

NFR-AF-001..004 and NFR-AF-008 are asserted in focused system scenarios and format/loader unit tests. NFR-AF-005 uses retained benchmark artifacts tied to binary and fixture hashes. NFR-AF-006 uses negative/fault-injection scenarios. NFR-AF-007 is enforced by MDSOC review, dependency checks, lint, duplication checks, and both direct-env/runtime guards.

