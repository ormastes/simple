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
module's `SdnValue` in its payload, but `SdnValue` is absent from the explicit
import list. HIR materializes the imported enum's public payload shape, so the
consumer must import that payload type directly instead of depending on an
unrelated package sibling's private import.

The existing side-branch attempt `ba55a61c5b46` imports the canonical std SDN
enum into `driver_api_core`; that is a different type and private sibling-import
leakage is intentionally no longer available. It is not a valid repair for the
backend-local payload.

## Required repair

- Import the backend-local `SdnValue` beside `BackendResult` and `BackendError`.
- Retain a behavioral HIR regression for explicit enum payload dependency
  resolution and the adjacent private-sibling non-leak case.
- Refresh Stage 3, retry Stage 4 with the existing cache, and keep no-stub
  fallback enabled.
