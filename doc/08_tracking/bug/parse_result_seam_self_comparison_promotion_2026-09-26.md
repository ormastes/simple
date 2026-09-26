# Parse-result seam self-comparison could qualify scalar promotion

**Found:** 2026-09-26. **Requirement:**
`doc/02_requirements/feature/environment_optimized_dynamic_libraries.md`
REQ-009, which requires independent canonical scalar parity before SIMD
promotion.

## Evidence

`src/compiler/80.driver/parse_result_provider_seam_v1.spl` defines its scalar
provider using `parse_and_build_module_scoped`. The direct leg of
`test/01_unit/compiler/driver/parse_result_provider_seam_v1_spec.spl` calls
the same function. The former test gave those legs different text identities
and asserted `default_promotion_qualified` from
`parser_scalar_parity_qualify_v1`. Distinct names therefore stood in for an
independent grammar/action engine. The normalized equality was a useful seam
regression check but could not satisfy canonical scalar promotion.

The SIMD unavailable receipt also named the author's AArch64 host as though
every runtime host had that architecture.

## Mitigation in this lane

`parse_result_parity_evidence_v1` now refuses the known flat-AST scalar slot
as a canonical leg, including a relabeled result retaining its implementation
identity. Its unit spec expects that refusal while retaining direct normalized
equality checks. The SIMD unavailable reason now describes the missing admitted
provider and mapped artifact without asserting host architecture.

## Remaining work

This does not provide the independent canonical Simple grammar/action engine.
The generic parity evidence structure still relies on caller-supplied
implementation identities; promotion must be connected to an authenticated
provider and an executed differential corpus before it can become a production
gate. Run the focused spec and required compiler/lib/MCP/LSP checks with a
source-matched pure-Simple tool once the macOS Cocoa bootstrap ownership gate
is repaired. Source review and whitespace checks alone are not runtime
qualification.
