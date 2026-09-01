# Versioned Codegen Backend Plugin

Source:
`test/03_system/app/compiler/feature/versioned_codegen_backend_plugin_spec.spl`

Manual mirror status: **partial source-contract manual; full runtime evidence
pending**.

## Purpose

Admit the LLVM/Cranelift backend boundary only when the versioned model,
descriptor admission, deterministic role selection, retained session, checked
loader, and identity-bound receipt are all present. Missing production source
is a hard failure, not a skipped fixture.

## Audience

Compiler, interpreter, bootstrap, and release owners reviewing the migration
from caller-specific backend factories to one versioned provider interface.

## Preconditions

- Run from the repository root with an admitted pure-Simple SSpec runtime.
- The six canonical production files exist:
  - `src/compiler/00.common/backend_plugin/model.spl`
  - `src/compiler/00.common/backend_plugin/receipt.spl`
  - `src/compiler/70.backend/backend_plugin/admission.spl`
  - `src/compiler/70.backend/backend_plugin/registry.spl`
  - `src/compiler/70.backend/backend_plugin/session.spl`
  - `src/compiler/70.backend/backend_plugin/loader.spl`
- An incomplete lane must remain visibly failed with
  `backend provider fixture unavailable`.

## Operator workflow

1. **select backend for execution role** — confirm the registry owns the
   Interpreter/JIT → Cranelift and Compiler/AOT → LLVM defaults, and that the
   loader delegates selection rather than naming providers.
2. **admit versioned provider** — confirm the 70-layer `admit_backend_plugin`
   owner delegates to `admit_backend_plugin_descriptor`, which checks descriptor
   size, ABI, provider version, MIR digest, roles, targets, and capabilities
   before a receipt records the complete provider identity.
3. **compile through backend session** — confirm the vtable advertises compile,
   finalize, and execute support and the session retains descriptor, handle,
   receipt, close, and closed-state ownership without direct factory or
   `rt_cranelift_*` access.
4. **reject incompatible provider without fallback** — confirm one resolution
   and one admission occur, the dynamic symbol is fixed to
   `simple_backend_plugin_v1`, errors return explicitly, and the loader cannot
   contain LLVM/Cranelift literals or a fallback backend.

## Observable results

All assertions are production source-contract assertions. The spec reads no
design document as its oracle, creates no substitute provider, and contains no
placeholder pass. Any missing file, missing compatibility field, altered role
default, direct provider access, repeated resolution/admission, or provider
literal in the loader fails the scenario.

## Requirement map

| Requirements | Evidence |
|---|---|
| REQ-001, REQ-008, REQ-010 | built-in compile coverage plus retained `BackendSession`; production caller migration remains open |
| REQ-002, REQ-006 | built-in descriptor admission and fixed dynamic entry lookup; typed dynamic activation remains open |
| REQ-003, REQ-004, REQ-005 | exact role defaults and centralized selection path |
| REQ-007 | single resolve/admit path with no provider literals or fallback owner |
| REQ-009 | provider identity, version, build, ABI, MIR, target, features, role, and optimization receipt fields |
| NFR-003, NFR-004 | no hot-path scan plus one retained built-in codegen object; dynamic lease/session retention remains open |
| NFR-005, NFR-007 | built-in explicit error path and deterministic receipt schema; dynamic leak/partial-artifact evidence remains open |

## Evidence and provenance

The executable source is the authority for these four structural scenarios.
Focused supporting specs cover real built-in LLVM/Cranelift compilation and
the direct-provider boundary scanner, but this manual does not claim the full
feature runtime or bootstrap gates have passed.

## Limitations

Native ABI lifecycle, canonical-MIR Simple transport, and CLI/cache identity
propagation now have focused evidence. The native lifecycle is open, compile,
finalize, diagnostics, copy, release, close, then unload. Cache provenance binds
explicit path policy and hashes selected provider bytes. Remaining blockers are
interpreter extern dispatch and admitted dynamic session activation. This
manual does not claim Phase 3 convergence.

This gate proves structural metadata and built-in fail-closed selection only.
The focused unit lane proves representative built-in compilation, while the
boundary scanner now recognizes raw `rt_jit_*`, `rt_exec_manager_*`, and
legacy direct compile helpers outside explicit owners. Production AOT/JIT
caller migration, typed dynamic descriptor invocation/open-session behavior,
artifact equivalence, provider-bound cache invalidation, Phase 3/4 linking,
latency, RSS, partial-artifact cleanup, and provider teardown allocation
evidence remain open gates in `doc/03_plan/versioned_codegen_backend_plugin.md`.
