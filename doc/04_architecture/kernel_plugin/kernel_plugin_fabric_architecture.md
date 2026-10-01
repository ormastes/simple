# Kernel Plugin Fabric Architecture

**Status:** Proposed
**Date:** 2026-09-03
**Baseline:** `43a4a491c3b5ab8bd350a09a2541a726213053a2`

## Decision

Kernel Plugin Fabric (KPF) is the reusable composition, admission, lifecycle, and bounded asynchronous dispatch nucleus for compiler providers, lint, IDE services, and MDSOC++ products. It extends, rather than replaces, `SimpleCompositionImageV1` and `SimpleProviderQueryV1`.

## Requirements

- **REQ-KPF-001:** One logical typed interface supports static-direct, static-table, native, SMF, worker, and optional Wasm placement.
- **REQ-KPF-002:** K0g contains only language-neutral IDs, fixed records, admission, bounded tables, lifecycle, dispatch, and receipts; K0c adds the minimum self-hosting compiler closure.
- **REQ-KPF-003:** SCI is the immutable composition authority and provider query is the native discovery authority.
- **REQ-KPF-004:** Stable ABI records contain fixed-width POD data, offsets, lengths, digests, and opaque handles; private Simple, Rust, and C++ objects never cross it.
- **REQ-KPF-005:** No-GC and no-allocation are independent declared properties; bounded profiles allocate before seal and perform no hidden run-phase growth.
- **REQ-KPF-006:** Persistent IDs resolve once to generation-local dense slots; steady-state dispatch performs no string, hash, manifest, filesystem, or symbol lookup.
- **REQ-KPF-007:** Generational handles, pins, cancellation, deadlines, backpressure, quiescence, and atomic publication prevent stale access and unsafe unload.
- **REQ-KPF-008:** Generated schemas produce Simple, C, Rust, C++, worker-wire, and optional WIT projections from one canonical source.
- **REQ-KPF-009:** Lint reports typed coverage and incompleteness; failure, no input, or skipped required analysis can never become clean.
- **REQ-KPF-010:** Native IDE and VS Code remain shells over one editor-neutral tooling session and authoritative language providers.
- **REQ-KPF-011:** Extended enums extend sealed data-constructor families only; provider discovery and capability namespaces use stable IDs/descriptors.
- **REQ-KPF-012:** MDSOC++ combines MDSOC boundaries, optional capsule-private ECS, KPF composition, capabilities, generations, receipts, and rollback.

## Kernel Boundary

| Layer | Owns | Forbidden dependencies |
|---|---|---|
| K0g common | identities, descriptors, status, wire records, receipts | parser, HIR/MIR, editor, LSP, JSON, filesystem scanning |
| K0g sync | admission, graph validation, dense tables, generations, pins | product semantics |
| K0g async | rings, arenas, requests, cancellation, deadlines, quiescence | language-native futures at ABI |
| K0c | K0g plus minimum parser/type/MIR bootstrap closure | optional policy/providers |
| Product providers | compiler, lint, IDE, application semantics | sibling-private state across boundaries |

Dependencies flow from products and placements toward K0g. `std.nogc_sync_mut.composition` remains below the asynchronous facade.

## Composition Axes

Closure and placement are independent:

```text
closure:   Static | Complete | Dyn
placement: Erased | StaticDirect | StaticTable | Native | SMF | Worker | Wasm
```

Critical compositions reject runtime-open `Dyn`, wildcard authority, unbounded memory, incompatible threading, and operations that violate declared no-allocation behavior. Complete native artifacts are valid when exact identities and digests are sealed before launch.

## Runtime Architecture

```text
typed declarations / *.kpf.sdn
          -> schema compiler -> bindings + registries + SCI projection
          -> composition sealer -> graph/capacity/capability proof
          -> admission -> prepared generation -> shadow -> atomic publish
          -> dense direct/table/native/worker dispatch
          -> drain -> retire after zero requests, pins, callbacks and buffers
```

The bounded substrate uses generational slot maps, fixed request/completion/event rings, bounded timers, host-owned arenas, and generation pin tables. Enqueue returns `Accepted`, `Coalesced`, `WouldBlock`, `CapacityExceeded`, or `Rejected`; it never grows implicitly.

## Product Projections

- **Compiler:** existing backend ABI is the first compatibility pilot; later providers reuse KPF lifecycle and receipts.
- **Lint:** coarse language providers expose stable fact/query capabilities; fine rules remain provider-local scheduled units. Rust uses Cargo/Clippy JSON and rust-analyzer workers; C++ uses compile databases, clangd, and clang-tidy workers.
- **IDE:** existing editor extension API becomes a compatibility facade. VS Code and SVIM/Simple IDE consume the same versioned document snapshots, diagnostics, fixes, tests, and commands.
- **MDSOC++:** a product sealer binds feature and layer facets, validates authority/memory/concurrency, and emits startup, upgrade, rollback, and proof artifacts.

### MDSOC++ product-generation authority

The IDE/tooling pilot uses one mutable product-generation owner. It prepares and
migrates candidate state before publication, then publishes the new active
generation and the old draining generation in one non-yielding owner method.
Readers therefore observe either the old pair or the new pair, never a mixed
composition/state binding. The old deployment and its exact state snapshot stay
retained while requests remain pinned. Drain completion retires that snapshot;
rollback is legal only before retirement and restores the retained deployment
and state together. Every accepted transition has a bounded retained receipt,
and insufficient receipt capacity rejects before publication.

## Safety And Failure Policy

- Configuration and SCI decoding are inert.
- Admission verifies path, digest/signature, target, ABI/schema, operations, capabilities, memory, concurrency, and trust before execution.
- Capabilities are scoped leases, not ambient authority.
- Untrusted or toolchain-coupled providers default to workers or Wasm.
- A candidate generation cannot replace the current generation until shadow gates pass.
- Unknown required fields or capabilities fail closed; optional append-only tails follow `struct_size` rules.
- Receipts record composition, generation, provider/toolchain identity, coverage, cache reuse, skips, failures, timings, and resource high-water marks.

## Architecture Acceptance

The architecture is accepted when every requirement maps to a design mechanism and migration gate; K0g import closure is mechanically checked; SCI/provider-query remain authoritative; and no product introduces a competing loader, registry, diagnostic truth, or plugin lifecycle.
