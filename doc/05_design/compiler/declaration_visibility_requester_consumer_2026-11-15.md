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
NamedImport hops in the same immediate folder are supported. Every admitted named
import must have a current child receipt joined to the exact import row target
and selected configured name; unavailable legacy hops are not grants. Terminal `pri` cannot be promoted;
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

## Safety repair and incomplete positive requirements

Complex imported aliases and generic default/bound dependencies do not yet retain their
actual declaration-owner binding selections. The outer consumer now reports
`alias-route-closure-unavailable` or `generic-route-closure-unavailable` before
owner-switch elaboration can skip checks. This is missing capability, not a
language rule declaring otherwise-valid aliases or defaults inaccessible.

Three required positive executable cases deliberately retain success oracles:
a public alias to a public target, a valid generic default, and an explicit
folder-local sibling facade export without a public implementation child. They
are known unsupported by this checkpoint and must not be rewritten to expect
denial. Full implementation requires selected alias target/default/bound binding
receipts under the declaring lexical scope (including neutral formals), and an
authenticated direct-folder/sibling import selection receipt from the configured
resolver. Parser spelling, matching physical target or matching folder alone
cannot mint that authority. Their traversal must join actual typed predecessor
edges and the same snapshot/configuration/generation before permitting access.

## Actual same-file alias selection producer

The existing bare nongeneric alias registration branch already registers a
non-alias target declared by the same surface and obtains its actual qualified
SymbolId. It now captures the returned target category only when that SymbolId
is exactly the binding installed for the source import. The module-local proof
retains alias/target declaration projections, source SHA, snapshot and both
registry generations. The requester joins those exact facts before accepting
the alias, rejects explicit-private targets, and recursively checks whether the
nominal target still requires unproved generic defaults or bounds. No parser
name-only scan manufactures the selected dependency. Module reset drops proofs.

The preexisting positive public `Alias = Target` requirement is now intended
supported by this source path (runtime remains UNRUN). General alias templates,
valid generic defaults/bounds and authenticated sibling import provenance remain
unfinished. The two corresponding positive success oracles remain unsupported.
