# Query boundary classification lost its function declaration

Status: source repair; native/compiler integration verification UNRUN.
Bug DB reconciliation: pending; no qualified full-CLI bug database tool available
in this bootstrap lane. This is a direct source restoration, not a workaround.

Introduced by700eba492ea (PR3537); present in release_phase3 at
1d8c3a5ab193f3c551483d29f203e0739c708b83. Removing adjacent duplicate
declaration helpers also removed `fn boundary_kind(owner_file: text) -> text:`
while retaining its body. Consequently domain_block_kind contains statements
referring to undefined owner_file, and hover/visibility consumers call a missing
boundary_kind function.

Restore exactly the original declaration immediately before its existing body.
The body still distinguishes open scopes, ordinary boundaries and bypass
boundaries. No API, classification rule or caller behavior changes are intended.

Existing behavioral regression coverage:

- test/02_integration/app/query_visibility_surfaces_spec.spl exercises hover,
  completion and document symbols through the public query visibility CLI.
  Its document-symbol scenario requires `"boundaryKind":"boundary"`.
- test/01_unit/app/cli/query_visibility_feature_spec.spl exercises visibility
  JSON and public feature classification using the real query helper module.

Validation in this repair lane: exact parent/current source inspection shows
the declaration existed before700eba492ea, is absent in1d8c3a5ab19, and is now
restored with its original signature. Production diff is one added line.
No new source-text mirror test was added; existing public behavior coverage
already checks the affected result. Test execution, whole compiler/lib/MCP/LSP
checks and production admission remain UNRUN. No native rebuild was launched:
the old bootstrap entry's three-build cap is exhausted and no usable full-CLI
verification runtime has been qualified in this lane.

## Prepared standalone native control

test/01_unit/app/cli/query_visibility_boundary_native.spl exercises the same
visibility_json adapter already imported by the existing visibility feature
spec. It uses real fresh caller-selected temporary files and distinct failure
strings for ordinary boundary/self reachability, open/public reachability,
sibling denial for an unexported boundary symbol, and bypass/public reachability.
It does not import boundary_kind directly, change production visibility, invoke
a full CLI child, initialize BDD, compare arrays, or use stubs. The production
repair remains exactly one restored declaration line. This fixture is prepared,
not compiled or executed; its first native qualification cycle awaits resource
authorization. A pre-existing fixture path is rejected and never deleted.

## Qualification fixture correction after cycle2

Cycle2 parsed72modules but one HIR entry failed; its terminal ledger records
query_visibility_boundary_native.spl as FAILED/UNCACHED. The child diagnostic
text was not retained, so the exact worker reason is not claimed. Independent
source review found exactly two literal `{Thing}` regions in the newly added
import-file content string. Ordinary Simple strings treat those as expression
interpolation. They are corrected to `{{Thing}}` so the emitted fixture file
contains literal braces. The intentional `{failure}` status interpolation stays.
This is a mistake in our new control, separate from the product boundary-header,
range-lowering and trailing-dot issues. No production line changes in this
correction. A final cycle3 requires owner review; no automatic retry occurred.
