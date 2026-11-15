# Selected-child requester regressions

Status: twenty authored executable cases; UNRUN. RED/GREEN execution is blocked by
the absence of an admitted general pure-Simple SSpec runner. The frozen policy
fixtures are injected test inputs, not evidence of driver/frontend authentication.

Executable: `test/01_unit/compiler/hir/module_child_requester_v1_spec.spl`.

| Actual HIR path | Expected behavior |
|---|---|
| Named type through public/private aliases sharing a target | Public succeeds; private reports `private-child` |
| Named export facade versus selected private implementation route | Facade succeeds; direct route is denied |
| Folder-local declaration exported explicitly | Facade promotes it; direct outside-folder access is denied |
| Same-ID rebind or changed policy | Stale provenance is denied |
| Sibling access to omitted versus `pri` declaration | Omitted remains folder-local; `pri` remains file-private |
| Public child under another closed ancestor | Ancestor remains closed |
| Namespace and containing-type expression | Rejected before public member resolution can bypass it |
| Local alias declaration elaboration | Imported private route remains checked |
| Legacy flat import without selected-child provenance | Existing behavior remains unchanged |

The suite exercises production parser, registry freeze, import binding writes and
actual named-type/expression lowering. It does not prove runtime execution,
qualified/glob-export authorization, cross-directory facade chains, all implicit
qualified-name fallbacks, or complete member/type access enforcement.

Safety review added two negative closure cases. Three further positive cases
retain the required success expectation and are KNOWN UNSUPPORTED on this source:
valid imported public aliases, valid generic defaults, and sibling facade export
without a selected public implementation-child receipt. A future run is expected
to expose these gaps; this suite is not currently claimed green or complete.

The follow-up same-file alias producer addresses the preserved public-alias
positive oracle. Two added cases reject an explicit-private selected alias
target and a corrupted proof, and check module-reset cleanup. All remain UNRUN.
The valid-default and sibling-facade positive cases are still known unsupported.

The selected nominal-default producer now addresses the preexisting bare valid
generic-default positive oracle. Three additional cases cover explicit-private
selected defaults, changed owner-qualified bindings/reset, and formal shadowing
that must not produce an unrelated nominal proof. All nineteen cases remain
UNRUN; the sibling-facade positive is still known unsupported. Other default
forms and bounds remain outside the supported producer slice.

A twentieth case removes the nominal template payload and requires unavailable
authority rather than treating missing metadata as an empty default list.

## Authenticated direct sibling source checkpoint (2026-11-15)

The unchanged legal `use physical.body.{Target}; export Target` success oracle now
has a production resolver branch. Canonical source admission retains its exact
namespace key; aliases cannot replace it. Inventory observations retain the
selected source SHA through SourceFile, driver ownership copy, frozen evidence,
semantic identity and promotion roots. The direct-folder-source receipt selects
that key before legacy resolution and requires both authenticated source hashes,
a shared snapshot, complete policy observations, and same immediate folder.
A registered namespace parent retains authority over child selection; failure
there cannot fall through into this branch. No implicit name-only sibling search
or canonical-path reconstruction is authorized.

The existing typed selected-export edge supplies import row/item, binding category,
role, projection and registry generation. The requester joins that edge to the
new route receipt and revalidates exact admission names, importer ownership,
policy digests, hashes, snapshot and route/registry generation. Explicit export
may promote omitted declaration intent within the selected sibling hop; explicit
pri remains denied. The external facade child and all crossed ancestors are
checked before this inner hop. A direct sibling receipt belongs only to its
actual importer; it is not external permission for the implementation module.

Six new negative cases cover private child aliases, explicit pri, stale source
inventory/admission namespace, closed ancestor, arbitrary same-path alias, and
rebound target. The earlier expected-success oracle is unchanged. Total consumer
cases: 26 authored, UNRUN. The nine receipt cases also remain UNRUN. Source hygiene
is separate from runtime RED/GREEN: no qualified SSpec producer exists in this
lane; no seed fallback, full build, or runtime PASS is claimed. Bounds, other
default forms, implicit sibling lookup, cross-folder/glob/qualified exports and
full visibility/runtime/lifetime/performance qualification remain incomplete.
