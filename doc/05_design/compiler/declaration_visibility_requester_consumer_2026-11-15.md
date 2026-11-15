# Bounded selected-child requester consumer

Status: implementation checkpoint; runtime, performance and full visibility
qualification pending. Extends receipt checkpoint `47c4abcc8e2`.

The selected requirements are route-specific access through actual configured
child receipts, explicit `pri` file privacy, immediate-folder omitted syntax,
explicit facade promotion where retained typed predecessors prove eligibility,
and no public child bypass of a separately closed ancestor.

## Ownership and actual use sites

Source import capture now retains selected category/name and a binding subject
(scope, spelling and symbol) alongside the mutation-version key and receipt.
A same-ID rebind still has tracked history but fails the current key comparison;
it cannot degrade to legacy absence. Module reset clears all parallel metadata.
Fresh lexical shadows select their own scope and do not borrow outer receipts.

`lower_named_kind` checks the actual selected binding before transparent alias
expansion. `lower_hir_expr` checks identifiers/qualified binding spellings before
lowering; call, struct and enum paths also check before specialized dispatch.
Namespace/containing-type denial therefore precedes member selection. Existing
member visibility remains separate. Internal imported declaration elaboration
is excluded; local source alias elaboration is checked.

A valid receipt is first joined with the selected frozen policy, current source
SHA, snapshot and registry/configured generations. The child modifier and every
crossed target ancestry observation are evaluated. Authenticated absence is open;
a present ancestor other than the one opened by this exact public-child receipt
is closed. No path-match search chooses another child.

A direct declaration retains its exact source intent. For a named-export facade,
the typed selected-export API supplies actual predecessor edges. Only Direct and
NamedImport hops in the same immediate folder are supported. Each admitted named
import's child receipt is checked when present. Terminal `pri` cannot be promoted;
omitted intent is eligible from the exporting folder and the explicit export
may expose it externally. An unavailable chain is denied, not guessed. Qualified
and glob export hops and cross-directory chains await their own route receipts.

Legacy bindings with no selected-child provenance retain existing behavior. This
is a deliberately bounded migration, not full language-wide enforcement.

## Cost and qualification limits

The zero-provenance path exits before binding lookup or dotted-expression walks.
Tracked subjects currently use a module-local linear lookup. Receipt validation
rehashes retained policy data at use time so same-epoch mutation cannot reuse a
cached permit. This favors fail-closed freshness for the initial unqualified
slice; no filesystem reads or whole source-tree scans occur. Export recursion is
bounded to depth 32 and a shared budget of 256 visited bindings/edges.

A production-performance admission still needs an immutable-owner invalidation
contract and indexed subject lookup, plus warm compiler/MCP startup, request
latency and max RSS evidence. No performance acceptance is claimed. General
compiler/core and MCP/LSP smoke checks remain blocked by the unavailable admitted
general runner. Do not publish or call this full visibility qualification.
