# Versioned backend plugin refactoring plan

<!-- codex-design -->

## Slice 0 — freeze behavior

Inventory every LLVM/Cranelift construction and direct call. Add characterization
tests for current interpreter and compiler defaults, explicit overrides, Phase 3
Cranelift symbol closure, and artifact receipts.

## Slice 1 — common contracts

Add ABI-safe request, descriptor, vtable, error, session, and receipt types.
Define ABI v1 constants and MIR digest ownership. No caller migration yet.

## Slice 2 — built-in adapters

Wrap current LLVM and Cranelift factories behind descriptors. Route both through
admission and `BackendSession`, initially without dynamic loading.

## Slice 3 — role-aware startup

Centralize defaults in `load_backend(request)`. Migrate compiler/AOT first,
then interpreter/JIT. Remove caller-local default and fallback decisions.

## Slice 4 — dynamic provider loader

Add checked `simple_backend_plugin_v1` resolution, library leases, ABI/MIR and
capability admission, and deterministic rejection diagnostics. Do not add new
raw dynamic-loader hooks outside the canonical SFFI owner.

## Slice 5 — eliminate direct access

Replace direct LLVM and `rt_cranelift_*` caller access with session operations.
Add a structural lint/gate preventing regression. Retain provider-private calls.

## Slice 6 — cache/provenance and Phase 3

Include descriptor identity in cache keys and receipts. Require Phase 3 to admit
the selected provider archive/library before link, proving both LLVM-default and
Cranelift-override builds.

## Slice 7 — convergence

Run focused unit/integration/system tests, then one Phase 2 → Phase 3 incremental
bootstrap for each backend. Measure startup/RSS, audit SFFI, and remove superseded
factories only after both lanes pass. Maximum three fix/verify cycles.

## Rollback

Each slice keeps the previous built-in adapter selectable until its replacement
passes. Rollback changes registry selection, not emitted artifact formats or
provider ABI.

