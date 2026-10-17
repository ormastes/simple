# Query boundary classification lost its function declaration

Status: source repair verified by the standalone native query control.
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
restored with its original signature. Header restoration is one added line;
the accompanying native path/import workarounds have separate bug reports.
No new source-text mirror test was added; existing public behavior coverage
already checks the affected result. Existing BDD integration specs, whole
compiler/lib/MCP/LSP checks and production admission remain UNRUN. The separate
query qualification lineage used its three permitted native build attempts.

## Standalone native control

test/01_unit/app/cli/query_visibility_boundary_native.spl exercises the same
visibility_json adapter already imported by the existing visibility feature
spec. It uses real fresh caller-selected temporary files and distinct failure
strings for ordinary boundary/self reachability, open/public reachability,
sibling denial for an unexported boundary symbol, and bypass/public reachability.
It does not import boundary_kind directly, change production visibility, invoke
a full CLI child, initialize BDD, compare arrays, or use stubs. The production
header repair remains exactly one restored declaration line. A pre-existing
fixture path is rejected and never deleted. The final native control passed as
recorded below; it is not the existing full-CLI/BDD integration suite.

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
correction. Owner review preceded the final cycle3; no automatic retry occurred.

## Final scoped native qualification

Qualified source: `3a3e5628c3cbe31d317ef299b0fc7f2fb666dbc5`.
Pure-Simple producer SHA256:
`0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b`.
Strict candidate SHA256:
`587c774f14d0c297e6f76b43c0e5a82b4c00c94cc9fdbb1cbba70a15defb1cc0`.

Cycle3 retained56 genuine SPL objects. Direct-object linking also retained
unused optional CLI wrappers and failed on unavailable runtime providers.
The final standard lazy archive contains all56 unchanged objects, with every
member's extracted bytes hashed against its original. The canonical entry
roots all8 actual module initializers;38 C runtime objects were compiled from
this checkout and reused only after source/header/object identity checks.
Strict archive linking exited0 with standard OPT:REF and no FORCE, ignored
unresolveds or stubs. Its map includes the real query/control functions and
excludes all44 unused optional CLI wrapper definitions.

The standalone control ran exactly once on fresh temporary files: exact PASS
line, exit0, empty stderr and unchanged candidate hash. It checks boundary,
open, sibling denial, bypass, peer-path tails and imported-module contents.
Evidence: `C:/dev/simple-bootstrap-storage/phase3-validation-20261016/query-boundary-native-cycle1/`
contains native-query-control-receipt.json and manual-clean-link archive proofs.
This verifies the reachable app CLI leaf behavior; it does not qualify a full
CLI, unavailable optional CLI capabilities, compiler generation admission,
package publication or deployment. Bug DB reconciliation remains pending.
