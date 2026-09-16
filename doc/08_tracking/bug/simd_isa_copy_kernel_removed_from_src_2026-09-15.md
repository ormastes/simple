# SIMD ISA copy kernel API removed from src
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_dispatch_spec.spl

## Observed
`simd_isa_copy_span` and `_kernel_probe_copy_bucket` no longer exist in
src/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider.spl or
backend_software.spl. The sibling simd_isa_provider_spec passes after an
import-prefix fix; only the copy-kernel dispatch spec stays RED.

## Unblock condition
Restore the copy kernel API or port the spec to the replacement dispatch
path with a reviewed mapping.

