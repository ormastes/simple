# Versioned LLVM/Cranelift backend plugin — main plan

<!-- codex-design -->

## Purpose

This is the canonical starting document for implementing the shared,
dynamically loadable LLVM/Cranelift backend interface. The main implementation
session should begin here and follow the linked artifacts rather than designing
a second interface.

## Selected behavior

- Interpreter/JIT defaults to Cranelift and may explicitly select LLVM.
- Compiler/AOT defaults to LLVM and may explicitly select Cranelift.
- Built-in and dynamically loaded providers implement one versioned contract.
- `load_backend(request)` is the sole startup/selection entry point.
- Compilation and execution use `BackendSession` only.
- Explicit/default provider admission fails closed; no silent backend switch.

## Authoritative documents

1. [Feature requirements](../02_requirements/feature/versioned_codegen_backend_plugin.md)
2. [Non-functional requirements](../02_requirements/nfr/versioned_codegen_backend_plugin.md)
3. [Architecture](../04_architecture/versioned_codegen_backend_plugin.md)
4. [Architecture TLDR](../04_architecture/versioned_codegen_backend_plugin_tldr.md)
5. [Detailed design](../05_design/versioned_codegen_backend_plugin.md)
6. [Refactoring plan](design/versioned_codegen_backend_plugin_refactor.md)
7. [System-test plan](sys_test/versioned_codegen_backend_plugin.md)
8. [Agent/lane plan](agent_tasks/versioned_codegen_backend_plugin.md)

## Main-session execution order

### Gate 0 — establish ownership and baseline

- Work in an isolated branch/worktree based on the intended bootstrap candidate.
- Inventory current `CodegenFactory`, backend selectors, LLVM calls,
  `rt_cranelift_*` calls, dynamic-loader facade, cache receipts, and Phase 3
  symbol-provider selection.
- Preserve unrelated dirty files and record the exact Phase 2 compiler identity.
- Run each baseline acceptance check no more than once.

### Milestone 1 — contract without behavior change

- Add `BackendRole`, `BackendPluginRequestV1`,
  `BackendPluginDescriptorV1`, `BackendPluginVTableV1`,
  `BackendPluginError`, `BackendSession`, and provider receipt types.
- Fix ABI v1 structure sizes, ownership, buffer release, MIR digest, and
  capability semantics in focused unit tests.
- Do not expose Simple or Rust trait objects across the dynamic ABI.

Exit: contract tests pass and existing backend construction remains unchanged.

### Milestone 2 — built-in adapters

- Wrap existing LLVM and Cranelift implementations behind admitted descriptors.
- Implement `load_backend(request)` for built-in providers.
- Keep current call paths available until equivalence tests pass.

Exit: both adapters compile representative MIR through `BackendSession` and
produce provider receipts.

### Milestone 3 — caller migration and defaults

- Migrate compiler/AOT first: default LLVM, explicit Cranelift.
- Migrate interpreter/JIT second: default Cranelift, explicit LLVM.
- Centralize CLI/environment projection in the driver; providers receive only
  the immutable request.
- Remove caller-local automatic fallback decisions.

Exit: role-default and explicit-override tests pass with no silent substitution.

### Milestone 4 — dynamic loading

- Resolve `simple_backend_plugin_v1` through the canonical checked dynamic
  loader and retain a library lease for the full session lifetime.
- Validate symbol, descriptor size, ABI, provider version, MIR digest, role,
  target, and capabilities before `open_session`.
- Add malformed/missing/incompatible provider rejection fixtures.

Exit: built-in and dynamic providers use identical admission/session behavior.

### Milestone 5 — Phase 3 and cache convergence

- Bind provider identity/version/build ID to artifact cache keys and receipts.
- Make Phase 3 admit the selected Cranelift or LLVM symbol provider before link.
- Add a structural gate banning direct provider access outside adapters/SFFI
  owners.
- Run one incremental Phase 2 → Phase 3 build for LLVM default and one for the
  explicit Cranelift override; do not rerun green gates.

Exit: both Phase 3 artifacts link, identify their provider, pass CLI smoke, and
show no cache reuse across incompatible provider identities.

### Milestone 6 — verification and cleanup

- Run focused unit/integration/system tests, SFFI audit, compiler/lib checks,
  startup latency, representative compile latency, and max-RSS measurement.
- Remove superseded factories/direct calls only after both provider lanes pass.
- Maximum three verify/fix cycles; report remaining blockers instead of looping.

## Required implementation evidence

- Requirement-to-test traceability for REQ-001 through REQ-010.
- LLVM-default compiler/AOT receipt and Cranelift-override receipt.
- Cranelift-default interpreter/JIT receipt and LLVM-override receipt.
- Negative ABI, MIR digest, capability, target, and unavailable-provider tests.
- Phase 3 link proof for both providers.
- Warm startup and request latency plus maximum RSS.
- No new raw dynamic-loader or backend SFFI ownership outside canonical owners.

## Scope exclusions

- Rewriting LLVM or Cranelift code generation internals.
- Automatically choosing a different provider after admission/compile failure.
- Passing language/runtime heap objects through the plugin ABI.
- Loading/unloading a provider for each function or hot request.
- Treating Rust seed execution as self-hosted Phase 3 evidence.

## Session handoff

Start the implementation session with:

> Implement `doc/03_plan/versioned_codegen_backend_plugin.md` milestone by
> milestone in an isolated worktree. Use the linked requirements, architecture,
> design, refactoring, system-test, and agent-task documents as authoritative.
> Stop after each milestone's exit gate, preserve incremental caches, never
> silently substitute LLVM/Cranelift, and cap verification at three cycles.

## Implementation status (2026-08-28)

- Milestone 1: implemented — ABI-safe metadata, typed admission errors, and
  deterministic provider receipts with focused contract coverage.
- Milestone 2: implemented. Built-in LLVM and Cranelift sessions retain one
  `CodegenFactory` adapter and compile representative MIR through
  `BackendSession`; focused coverage also rejects unmapped target text without
  provider fallback.
- Milestone 3: request projection and role defaults are implemented, but
  production caller migration is not. Compiler/AOT still calls legacy direct
  compile helpers, and interpreter/JIT still calls `rt_jit_*` and
  `rt_exec_manager_*` owners without an admitted `BackendSession`.
- Milestone 4: checked `DynLib` load, exact `simple_backend_plugin_v1` lookup,
  and library lease are implemented. The explicit C ABI v1 header,
  generated-compatible Simple wire DTOs, and a loadable provider/host fixture
  now freeze typed operations and buffer/session lifetime. Native lifecycle,
  canonical MIR transport, CLI propagation, and cache path/content identity
  are complete. Interpreter extern dispatch and dynamic session activation
  remain fail-closed and pending; Phase 3 convergence is unproven.
- Milestone 5/6: the explicit-file structural boundary audit rejects direct
  LLVM/Cranelift provider calls, raw JIT/execution-manager calls, and legacy
  compile helpers outside their explicit adapter/SFFI/helper owners. It is not
  yet wired over the production caller set. Cache-key binding, Phase 3 provider
  admission/link convergence, latency/RSS evidence, and full verification
  remain open.

Verification checkpoint: focused common, driver, built-in compile-adapter, and
boundary-scanner specs pass. The canonical
32-worker Stage-2 incremental build reached compiler construction but timed out
on the pre-existing `src/compiler/10.frontend/core/__init__.spl` 300-second
per-file limit; its warmed cache may be retried once after the final source
snapshot stabilizes.
