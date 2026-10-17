# RT HIR blob validation can admit an incomplete inventory

- Bug: BUG-RT-HIR-BLOB-VALIDATION-FAIL-OPEN-20261017
- Status: source repair prepared; executable verification UNRUN; database registration pending.
- Affected source: 3078d75230b1d04fbea6cfe00fd9fab80be37564.
- Owner: src/compiler/35.semantics/rt_criticality_validation.spl, validate_rt_criticality_diagnostics_blobs.

The encoded-module adapter silently discarded failed HIR decodes and failed re-encoding comparisons, then ran RT policy on the surviving array. One damaged blob could therefore become an empty or partial policy universe. Before decoding, an additional success shortcut trusted parallel HAL flags and claim counts. Those hints had no binding to encoded module owners; false, extra, or negative values could suppress validation entirely.

The repair preserves the public arguments and the empty-blob real-module fallback. Nonempty input must decode and roundtrip every supplied blob before the complete restored array reaches the existing RT policy. The first decode or canonical-roundtrip failure clears previously published bound capabilities and returns a real Error diagnostic with its zero-based input slot. Parallel scalar hints no longer authorize success.

This does not repair the previously reported native large-HIR aggregate transport defect. If complete validation encounters that defect, the native failure remains a failure; admission must not skip modules to conceal it. This function also cannot establish that a caller supplied every project module: it receives no independently authenticated expected inventory. External missing-owner/duplicate-owner authority remains outside this bounded transport repair.

The real RT unit spec adds malformed input with false/missing/extra/negative hints, a corrupt late blob following a genuine encoded module, truncation and stale-capability clearing, a valid no-claims module, a real critical allocation claim with false hints, and the existing real-module fallback. These assertions use production codecs, registry and validation APIs. No fabricated codec, synthetic return, or source-pinning assertion substitutes for execution. An additional real noncanonical-wire control changes the encoded zero import count to 00, asserts successful legacy decoding and canonical re-encoding before requiring NONCANONICAL Error and stale-capability clearing. This control is source-reviewed only until executed.

Verification: independent source review of the production repair and all eight controls found no P0/P1. All new runtime controls remain UNRUN. No full compiler/core/MCP/LSP admission or release qualification is claimed. The provisional Phase3 diagnostic candidate is separate and unchanged.