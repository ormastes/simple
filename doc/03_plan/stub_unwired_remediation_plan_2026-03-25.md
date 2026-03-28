# Stub and Unwired Remediation Plan

**Status:** In Progress  
**Date:** 2026-03-25  
**Scope:** `src/` and actionable `examples/` paths that currently expose dummy behavior, fake-success flows, or unwired runtime contracts

---

## Summary

This plan turns the repo-wide stub/unwired audit into an execution document. The priority is not to implement every unfinished subsystem immediately. The priority is to make unsupported behavior honest, remove fake-success paths, and then incrementally wire the remaining high-value features.

The first implementation slice is complete:

- backend lowering for unsupported async, actor, GPU, VHDL, and SIMD ops now fails hard instead of emitting placeholder IR or zero values,
- browser TLS no longer pretends to establish a successful secure connection,
- the Torch example surface now raises explicit unsupported errors for major FFI-dependent placeholder APIs.

The remaining work is concentrated in three areas:

1. browser example bridges that still simulate success or expose placeholder object/runtime behavior,
2. Torch example API surface that is still broader than the real runtime support,
3. lower-priority runtime and OS areas where placeholders need honesty checks rather than feature completion.

## Goals

- Remove fake-success behavior from product-like code paths.
- Make unsupported features fail deterministically with explicit messages.
- Narrow example APIs where implementation is not real yet.
- Preserve intentionally incomplete educational/demo code only when it is clearly marked and not user-misleading.

## Non-Goals

- Completing every unfinished backend, browser, or ML subsystem in one pass.
- Replacing explicit “unsupported” behavior with full runtime implementations where the dependency stack does not exist yet.
- Refactoring unrelated dirty worktree areas outside the targeted stub/unwired paths.

## Completed Slice

### 1. Compiler/backend honesty

**Implemented**

- [`src/compiler/70.backend/backend/mir_to_llvm.spl`](../../src/compiler/70.backend/backend/mir_to_llvm.spl)
  - unsupported async/actor/GPU/VHDL/SIMD lowering now emits a hard panic path instead of placeholder IR or zero-value stand-ins.
- [`src/compiler/70.backend/backend/c_backend_translate.spl`](../../src/compiler/70.backend/backend/c_backend_translate.spl)
  - unsupported async/actor/GPU/VHDL/SIMD lowering now emits `spl_panic(...)` instead of fake-success C output.
  - removed the stale scalar SIMD fallback helper.

**Result**

- unsupported MIR operations no longer silently degrade into “successful” generated code on these backends.

### 2. Browser TLS honesty

**Implemented**

- [`examples/browser/feature/net/tls.spl`](../../examples/browser/feature/net/tls.spl)
  - handshake now returns explicit failure until TLS wiring exists,
  - certificate verification now rejects the unwired trust-chain path instead of pretending success.
- [`examples/browser/entity/net/tls_types.spl`](../../examples/browser/entity/net/tls_types.spl)
  - switched TLS config and certificate chain containers to plain arrays for stable runtime behavior.
- [`examples/browser/test/net/tls_spec.spl`](../../examples/browser/test/net/tls_spec.spl)
  - added regression coverage for honest handshake failure and trust-chain failure behavior.

**Result**

- browser TLS no longer presents a successful secure connection when no real TLS handshake or trust-chain verification exists.

### 3. Torch example API narrowing

**Implemented**

- [`examples/07_ml/torch/lib/torch/mod.spl`](../../examples/07_ml/torch/lib/torch/mod.spl)
  - explicit unsupported errors now replace clone/no-op placeholders for:
    - autograd operations,
    - reshape/view/transpose-family methods,
    - several NN layers,
    - optimizer `step()` methods,
    - `no_grad`, `set_seed`, and related FFI-dependent utilities.

**Result**

- the Torch example surface is narrower but honest about what the runtime actually supports.

## Remaining Work

## Phase 1: Browser Example De-dummification

**Priority:** P1  
**Goal:** remove remaining browser example paths that present successful flows without real runtime wiring

### Targets

- `examples/browser/transform/*`
- `examples/browser/feature/script/web_api/*`
- `examples/browser/feature/net/fetch.spl`
- `examples/browser/feature/net/cache.spl`
- `examples/browser/feature/net/h1_client.spl`
- `examples/browser/feature/net/h2_client.spl`
- `examples/browser/feature/net/websocket_client.spl`
- related browser tests under `examples/browser/test/`

### Tasks

1. Identify successful placeholder flows in DOM/script/network/compositor bridges.
2. Replace fabricated object references, successful no-op dispatch, and placeholder connections with explicit unsupported/failure results.
3. Keep unit-style model logic that is internally consistent and not user-misleading.
4. Add or repair specs for each corrected honesty boundary.

### Acceptance Criteria

- no browser network/security flow reports success without a real runtime path,
- no browser bridge fabricates external resources or successful side effects,
- updated browser specs pass for each corrected path.

## Phase 2: Torch Example Surface Reduction

**Priority:** P1  
**Goal:** finish converting the Torch example from “API-shaped placeholder library” to an honest staged example

### Targets

- `examples/07_ml/torch/lib/torch/mod.spl`
- `examples/07_ml/torch/basics/*`
- `test/feature_new/dl_examples_system_spec.spl`

### Tasks

1. Audit remaining methods that still describe placeholder or future FFI-backed behavior.
2. For each method:
   - keep it if implemented from existing tensor arithmetic/runtime support,
   - mark it unsupported if it still depends on missing FFI/runtime features.
3. Update example docs and sample programs so “stub mode” is explicit and local to the example runner, not implied as real library capability.
4. Add targeted tests where the test infrastructure can validate unsupported behavior cleanly.

### Acceptance Criteria

- no Torch example API silently returns clones/no-ops for unsupported operations,
- docs and examples do not overclaim feature support,
- remaining supported methods are internally consistent with the actual runtime.

## Phase 3: Runtime and OS Honesty Audit

**Priority:** P2  
**Goal:** verify that lower-level transitional code is either clearly internal/WIP or explicitly unavailable

### Targets

- `src/os/*`
- compositor/runtime support code under `src/lib/nogc_sync_mut/*`
- selected bootstrap-safe factory/shim modules in `src/`

### Tasks

1. Triage `return false`, placeholder allocation, and mock-device code paths into:
   - valid guard/failure behavior,
   - internal transitional code,
   - user-visible fake-success behavior.
2. Convert user-visible fake-success paths into explicit failures.
3. Leave clearly internal WIP code alone unless it leaks outward through public behavior.

### Acceptance Criteria

- public-facing runtime/OS paths do not silently claim live support that does not exist,
- internal stubs remain acceptable only when they are not externally misleading.

## Implementation Order

1. Browser example bridges
2. Torch example completion
3. Runtime and OS honesty audit

This order is intentional:

- browser example paths are the most user-visible remaining fake-success cluster,
- Torch has a smaller surface and a clearer unsupported-vs-supported split,
- runtime/OS work is broader and should be driven by confirmed outward-facing issues rather than raw placeholder count.

## Test Plan

### Completed verification

- `src/compiler_rust/target/debug/simple test examples/browser/test/net/tls_spec.spl`

### Planned verification

1. Add browser specs for each corrected bridge or network path.
2. Extend Torch example coverage where unsupported behavior can be asserted.
3. Add backend-facing tests that confirm unsupported MIR features fail deterministically instead of lowering to placeholder code.
4. Re-run targeted example/system tests after each phase rather than relying on grep-only validation.

## Risks

### 1. Placeholder count vs product risk

The repo contains many placeholders that are harmless internal scaffolding. Chasing all placeholders uniformly would waste time. This plan prioritizes user-visible fake-success behavior instead.

### 2. Test infrastructure gaps

Some areas, especially backend lowering and Torch unsupported behavior, are harder to validate through current direct tests. Where that remains true, the immediate fallback is targeted regression coverage plus explicit code-path hardening.

### 3. Example scope creep

The browser and Torch trees are large enough that “finish all unwired code” can expand indefinitely. Each phase should close a concrete cluster of misleading behavior rather than attempting full feature completion.

## Success Criteria

This plan is complete when:

- unsupported features fail honestly instead of simulating success,
- examples only advertise behavior that the runtime actually provides,
- remaining stubs are either internal, clearly marked, or protected behind explicit unsupported boundaries.
