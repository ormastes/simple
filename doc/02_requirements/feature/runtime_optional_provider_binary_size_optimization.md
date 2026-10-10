# Runtime Optional Provider and Binary-Size Optimization Requirements

## Selected variation extension — 2026-10-11

The user's instruction to apply the integrated SIMD/GPU/SOSIX proposal selects the following compatibility constraints. Existing REQ-001..015 and NFR-001..007 remain in force with unchanged budgets. These are requirements, not implementation claims.

- **REQ-016:** Reuse existing environment snapshots, target profiles, feature/target registries, catalog, admission, binding and generation owners; preserve negotiated ABI/schema compatibility.
- **REQ-017:** Use the existing sparse `variants/` resolver and `config/var.sdn`; normalize legacy SIMD roots into one selection/cache decision. No copied generic 32/64-bit or OS algorithm families.
- **REQ-018:** Distinguish output target, execution process, worker vector state and device generation. Admission requires exact ISA/OS/ABI/layout/policy legality; width or target flags cannot establish execution support.
- **REQ-019:** Preserve one operation/numerical/effect contract and shared vectorizer/planner. Fixed/scalable SIMD and SIMT retain distinct legal lowering; unavailable hard requirements fail visibly without unsafe fallback.
- **REQ-020:** Reuse common SOSIX/SimpleRing operation, result/wake, lease and retirement contracts. Sync/async and GC families share semantics; timeout/cancel cannot free live buffers and unload waits for pins/retirement.
- **REQ-021:** Keep arithmetic dispatch prepared and direct, with no added ring hop, discovery, CPUID or filesystem work inside hot loops. Share only target-independent cached work; record valid cache projections.
- **REQ-022:** Separate GPU compile artifacts from device execution; use existing emitters and native providers, not another runtime/resource manager. Qualcomm CPU, Adreno and Hexagon/HVX are independently admitted domains.
- **REQ-023:** Migrate by redirecting/moving existing owners with parity and rollback, then retire duplicates. Record declared, accepted, compiled, linked/loaded, bound, executed, equivalent and measured stages independently.

Acceptance extensions I5-V01..V08 are planned in the existing Item 5 acceptance document. Missing native tests remain open; no source-only check discharges these requirements.

Status: selected by user on 2026-09-02.

## Functional Requirements

- **REQ-001:** Registering an optional library must not load, map, initialize, link, decompress, scan, or start it.
- **REQ-002:** An optional provider loads only on first demanded capability after ABI, target, architecture, digest, dependency, and policy admission.
- **REQ-003:** Startup uses the exact entry dependency closure; unused arguments, optional libraries, providers, compiler backends, and tools are absent.
- **REQ-004:** Prefer a stable pure-Simple implementation. During stabilization, deterministic dual mode retains both pure-Simple and foreign providers with explicit selection, parity evidence, and rollback.
- **REQ-005:** Dual mode must never execute both providers for an effectful operation. Shadow comparison is permitted only for pure, bounded operations.
- **REQ-006:** Provider promotion requires correctness, mutation, performance, resource, architecture, and failure-parity evidence.
- **REQ-007:** NoGC programs that allocate nothing must not link or initialize collector code.
- **REQ-008:** `release-small` omits exceptions, unwind tables, RTTI, and their libraries only when closure proof establishes they are unnecessary.
- **REQ-009:** A foreign provider requiring exceptions, unwind, or RTTI is isolated in a demand-loaded provider artifact and cannot enlarge the base executable.
- **REQ-010:** Debug and ordinary release profiles retain required diagnostics; release-small is a distinct profile, not a global feature deletion.
- **REQ-011:** Every language feature and supported architecture remains available when demanded.
- **REQ-012:** Dynamic-provider absence or rejection produces the same typed Simple error contract as the corresponding unavailable capability.
- **REQ-013:** Native closure and loader receipts name every retained module, section, provider, dynamic library, constructor, export, and metadata root with a reason.
- **REQ-014:** Link output retains a map, removed-section log, section sizes, symbol-size ranking, dynamic dependency list, and stripped/unstripped hashes.
- **REQ-015:** Pure-Simple libraries are compiled as independently loadable sealed SMF/provider sections and are not reparsed from source on demand.

## Non-Functional Requirements

- **NFR-001:** Same-host NoGC hello unstripped executable is below 2 MiB on every supported native target.
- **NFR-002:** Linux ELF release-small NoGC hello is at most 15 KiB and no larger than 1.05 times a same-host, same-toolchain C hello with the same startup wrapper, required core runtime archive, linker options, section GC, and strip policy. The C user entry prints the same bytes through `puts`; the Simple user entry uses the required Simple print path. A bare C `main` is an advisory size comparison, not the ratio denominator.
- **NFR-003:** On non-ELF targets, release-small NoGC hello is no larger than same-host C plus a target-specific admitted fixed format allowance; the allowance may not hide retained runtime features.
- **NFR-004:** Minimal interpreter warm hello startup and max RSS are no worse than the admitted same-host Python baseline by more than 10%; the target is parity or better.
- **NFR-005:** A no-import hello loads zero optional provider DSOs and performs zero optional-provider initializations.
- **NFR-006:** Demand-loading one provider adds no unrelated provider dependency and does not change results or errors on any architecture.
- **NFR-007:** Size and startup gates use at least 30 samples for development and 100 for release, with p50/p95, RSS, binary hashes, toolchain identities, and checksums.
