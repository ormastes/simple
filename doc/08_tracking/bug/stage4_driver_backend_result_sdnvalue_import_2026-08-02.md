# Stage 4 driver BackendResult payload import gap

Status: open  
Severity: P1 bootstrap blocker  
Fix owner: `/root/stage4-driver-backend-result-import` — CLAIMED

## Reproduction

After the directory-package sibling-import leak was fixed at `06547b0fba9c`,
the no-stub x86 Stage 4 build parsed all 1,430 modules and stopped after 54 HIR
modules:

```text
error: focused native-build: HIR lowering error in
src/compiler/driver/driver_types.spl: unresolved type: SdnValue
```

Retained log:
`build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage4-native-build-hir-sibling-boundary.log`.

## Root cause

`driver_types.spl` explicitly imports `BackendResult` and `BackendError` from
`compiler.backend.backend_types`. `BackendResult.SdnData` exposes that same
module's backend SDN payload in its public shape, but the payload type is absent
from the explicit import list. HIR materializes the imported enum's payload
shape, so the consumer had depended on an unrelated package sibling's private
import.

The underlying ambiguity is a stale collision regression: the documented
`BackendSdnValue` and `DriverInitSdnValue` repairs existed in orphan commit
`e18937e064f` but were not on `main`, although the collision audit said they
were fixed. Current source again declared both as `SdnValue`, colliding with the
canonical configuration SDN enum. `CompiledUnit` is also multiply declared, so
the driver must import the backend owner explicitly when it imports
`BackendResult`.

The existing side-branch attempt `ba55a61c5b46` imports the canonical std SDN
enum into `driver_api_core`; that is a different type and private sibling-import
leakage is intentionally no longer available. It is not a valid repair for the
backend-local payload.

## Required repair

- Restore the backend and driver-local names `BackendSdnValue` and
  `DriverInitSdnValue`, including their exports and internal references.
- Import backend-owner `BackendSdnValue` and `CompiledUnit` beside
  `BackendResult` and `BackendError`.
- Remove the dead `Span` and canonical `SdnValue` imports from
  `driver_api_core`; none of its re-exported signatures exposes either type.
- Retain a behavioral HIR regression for explicit enum payload dependency
  resolution and the adjacent private-sibling non-leak case.
- Refresh Stage 3, retry Stage 4 with the existing cache, and keep no-stub
  fallback enabled.

## Focused verification

The behavioral regression
`test/01_unit/compiler/driver/backend_result_payload_identity_spec.spl` passes
both scenarios in interpreter mode. The collision audit also reports no
remaining enum-versus-struct/class `SdnValue` collision. Stage 4 remains the
authoritative closure gate, so this bug stays claimed until that build crosses
the former HIR boundary and produces its candidate.
