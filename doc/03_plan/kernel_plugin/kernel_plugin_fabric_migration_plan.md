# Kernel Plugin Fabric Migration Plan

**Status:** Proposed  
**Date:** 2026-09-03  
**Strategy:** Compatibility adapters, shadow execution, reversible cutover.

## Non-Negotiable Gates

- One owner freezes the V1 schema prefix before downstream generated-code work.
- SCI and `SimpleProviderQueryV1` remain authoritative; runtime never compiles a missing production plugin.
- No product may create a competing loader, lifecycle, registry, or diagnostic verdict.
- Every clean checker verdict proves nonzero required coverage.
- Every wave preserves rollback until parity, mutation, fault, and performance gates pass.

## Wave 0 — Evidence And Contract Freeze

Deliver K0g/K0c import boundary, registry inventory, IDs/versioning rules, current ABI/layout fixtures, lint false-clean fixtures, editor behavior fixtures, and startup/allocation/dispatch baselines.

**Gate:** REQ-KPF-002/003 are mechanically checkable; deliberately broken analysis cannot pass the shadow coverage predicate; no shared ABI implementation starts before approval.

## Wave 1 — Schema And Canonical ABI

Implement minimal SDN parser/canonicalizer, IDs/digests, layout generator, compatibility checker, common descriptors/status/receipts, static registry format, and Simple/C/Rust/C++ conformance bindings.

**Gate:** REQ-KPF-004/008; deterministic regeneration; cross-language layout equality; malformed/truncated/reserved/collision/compatibility fixtures fail correctly.

## Wave 2 — Bounded Runtime And Placements

Implement fixed generational tables, arenas, submission/completion rings, deadlines, cancellation, quiescence, atomic generations, static-direct/table adapters, then native/SMF adapter and worker supervisor.

**Gate:** REQ-KPF-001/005/006/007; zero post-activation allocation in strict profile; O(1) lookup/pin/cancel; stale handles and unsafe unload rejected; prior generation survives failed candidate.

## Wave 3 — Backend Pilot

Generate a KPF backend facet, adapt the existing backend V1 ABI, retain sessions across batches, add caller-owned output, and compare direct, legacy bridge, in-process KPF, and worker results/receipts.

**Gate:** static/dynamic parity; bootstrap/backend tests pass; no per-module load/session churn; rollback path remains live.

## Wave 4 — Unified Lint Kernel

Add canonical diagnostics, edits, coverage, verdicts, deterministic merge, generated rule descriptors, fact planner, output adapters, and Simple shadow migration. Then converge semantic `check`, add Rust Cargo/Clippy/rust-analyzer workers, and C++ compile-database/clangd/clang-tidy workers.

**Gate:** REQ-KPF-009; mixed-language deterministic result; warning, incomplete, no-input, crash, timeout and cancellation are distinct; sabotage/mutation tests prevent false clean; toolchain/build identity is receipted.

## Wave 5 — IDE Service Kernel

Adapt current extension manifests, commands, events, disposables, activation, permissions, and crashes to KPF. Add shared versioned tooling sessions, real worker execution, LSP/DAP/test adapters, generated VS Code contributions, and SVIM/native clients.

**Gate:** REQ-KPF-010; identical canonical results across native and VS Code clients; stale snapshots cannot publish; fallback is visibly degraded; unrelated workers do not start.

## Wave 6 — Extended Enum And MDSOC++

Generate constructor operation-completeness tables and dense tags; enforce Static/Complete/Dyn policy. Add MDSOC++ capsule schema, dependency/authority/memory/concurrency checks, state migration, upgrade and rollback proof. Pilot one large userland subsystem.

**Gate:** REQ-KPF-011/012; missing operation, illegal Dyn, dependency cycle, authority violation, or budget mismatch fails seal; kernel/drivers remain MDSOC-only.

## Wave 7 — Hardening And Optional Wasm

Add shared-memory worker optimization, signatures/revocation, fuzzing, crash loops, long-run allocation tests, benchmark CI, WIT generation/component host, SDK examples, and migration documentation.

**Gate:** static/native/worker share conformance corpus; optional Wasm round-trips canonical fixtures; security/fault/performance thresholds pass with recorded environment.

## Acceptance Matrix

| Requirement | Primary wave | Required evidence |
|---|---:|---|
| REQ-KPF-001 | 2 | placement parity corpus |
| REQ-KPF-002 | 0 | K0g import-closure check |
| REQ-KPF-003 | 0, 2 | SCI/query authority test |
| REQ-KPF-004 | 1 | ABI layout and forbidden-type audit |
| REQ-KPF-005 | 2 | allocator/capacity instrumentation |
| REQ-KPF-006 | 2 | steady-state lookup counters and scaling |
| REQ-KPF-007 | 2 | race, stale handle, pin and rollback tests |
| REQ-KPF-008 | 1 | deterministic generators and four-language corpus |
| REQ-KPF-009 | 4 | coverage, mutation and verdict tests |
| REQ-KPF-010 | 5 | editor-neutral client conformance |
| REQ-KPF-011 | 6 | closure/completeness negative tests |
| REQ-KPF-012 | 6 | capsule seal/upgrade/rollback pilot |

## Performance Gates

- Static coarse operation: no meaningful regression beyond 1% versus direct call.
- Admitted in-process batch: at most 5% framework overhead versus direct vtable batch.
- Strict hot path: exactly zero allocations after activation.
- Steady state: zero manifest/string/hash/symbol/filesystem lookups.
- Queue/table memory: fixed at admitted capacity.
- Startup: installed composition image only; no workspace plugin-directory scan.

## Cutover And Rollback

Each product progresses `legacy -> adapter -> shadow -> opt-in -> default -> deletion`. Publication is generation-atomic. Legacy code is deleted only after production caller reachability proves the new path is authoritative and the prior generation remains a tested rollback until the final deletion gate.
