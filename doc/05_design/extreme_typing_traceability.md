# Extreme typing and traceability: detail design

Status: proposed implementation contracts, 2026-11-01. Read the
[architecture](../04_architecture/extreme_typing_traceability.md) for ownership
and [selected policy](../02_requirements/feature/extreme_typing_traceability.md)
before this document. Identifiers here name proposed interfaces; they do not
assert existing functions or executable CLI support.

## Contracts and algorithms

| Proposed contract | Required data and invariant |
|---|---|
| `PublicSurfaceGraph` | Compilation subject, compiler/type-universe ID, effective export root IDs, canonical type nodes, visibility paths, substitutions, generated origin chain and completeness. One authoritative graph per publication candidate. |
| `TypeIdentity` | Compiler-owned stable-in-subject identity plus nominal declaration identity and instantiated arguments; never equality by pretty-printed spelling. Cross-revision matching records uncertainty. |
| `ExposureResult` | Safe / Violates / Unknown; export-to-leaf paths, canonical leaf, spans, surface digest and policy digest. Multiple diagnostics deduplicated by root/type/path identity. |
| `AssuranceRulePolicy` | Existing resolved assurance policy plus named `extreme_public_api` version, builtin catalog, domain-bound semantics, unknown handling and gate disposition. |
| `PublicationDecision` | Candidate/engine/policy/surface identity, check phase, allowed/denied/unknown, diagnostics and cache evidence. Public record fields alone do not establish unforgeable authority. |
| `TraceSnapshotIndex` | Snapshot/generation/schema/rule identity; nodes by ID/kind, forward/reverse typed adjacency, semantic symbol references, validity/completeness diagnostics. |
| `TraceQueryV2` | Operation, snapshot, roots, direction, allowed relations, precision filters, depth, limit, cursor and trusted visibility context. |
| `TraceViewProjection` | Canonical selected ID, subject, ordered rows/edges, annotations, paths, counts, omitted frontier, provenance and independent page/graph/qualification states. Pure computation. |
| `CodeRelationFact` | Compiler symbol endpoints, relation kind, exact/bounded_set/heuristic/unknown, static/observed distinction and expansion provenance. |
| `WorktreeOverlay` | Registered session identity+generation, immutable base/head/index/dirty subjects, capture state and typed semantic deltas. |

Exposure processing resolves export closure first, then substitutes canonical
types. DFS/SCC processing memoizes `(TypeIdentity, substitution, boundary,
policy)`; a processing set identifies cycles without declaring them safe.
Strongly connected transparent aliases without a resolved base are Unknown.
Recursive nominal types may be Safe only after all observable members and
generic arguments satisfy the policy. A compiler-trusted opaque marker stops
private representation traversal, not traversal of exposed operations.

Check explicitly public and implicitly exposed signatures alike: synthesized
constructors/accessors, equality/comparison/operator hooks, inherited/forwarded
methods, conversion/unwrap views, trait defaults and associated types. Raw
bool/text returns from derived public methods violate the selected rule.
Compiler-private intrinsic operations are outside the external API root set.
Only compiler identity establishes a builtin or nominal boundary; casing and
alias spelling are irrelevant. Unresolved external types, truncated expansion
or missing generic guarantees produce Unknown. Diagnostic traversal has
separate node/edge/path-size limits; robust+ Unknown denies publication.

Build candidate engine state without running user code. Analyze resolved
exports, expand/weave, specialize, analyze any changed/generated surface, then
commit the artifact or activate the module. Driver, loader and interpreter
adapters supply the same typed policy. Cache a decision only when compiler,
type-universe, source/dependency surface, generation, policy and engine ABI
digests match. A weaker-policy cache result is never reused as robust evidence.

## Easy semantic type creation is a delivery gate

Existing design documents specify `newunit Name: Base as suffix` in
[world units/newunit](language/language_features/types/world_units_newunit.md).
The parser's `core/_ParserDecls/enum_module_body.spl` registers newunits through
`core/types.spl:newunit_register`; registry/reset specs exist. These are source
observations, not proof that literal lowering and all execution engines work.
The system spec's historical RED note must not be relabeled as a current run.

E3 must demonstrate declaration, typed literal resolution, range diagnostics,
distinct nominal identities, import/reexport, container/callback use and actual
engine execution. Compile-time typed literal conversion does not require a
public function taking a raw primitive. Keep storage private and expose only
domain-safe operations; a generated primitive getter or raw constructor is a
bug. Use measurement units for real dimensions; use nominal newunit/opaque
types for identities and statuses. Do not prescribe wrapping `Option<i64>` as
a solution because its leaf is still bare. Text/char/bool ergonomics need real
semantic construction cases, not an untested numeric-only migration story.

## Query and storage behavior

Snapshot extraction is effectful; querying is pure. Publish a new index
generation only after validating IDs, relation endpoints, contains acyclicity,
symbol references and completeness diagnostics. Keep the last valid generation
on interrupted extraction, visibly marked stale. Missing/unauthorized content
is not an empty graph and cannot satisfy obligations.

Build adjacency in O(V+E), sort once by stable relation/endpoint identity and
retain reverse maps. Bounded BFS costs O(visited vertices + visited edges);
high fan-out hits an explicit work limit. Return one deterministic shortest
path for `path`; a bounded path set may be a later explicit mode. `walk`
returns typed reachable facts, `impact` explains reverse dependency paths and
`gaps` reports missing declarations, unknown resolution or unqualified
obligations separately. No command infers a verified result from a link.

Cursor payload is versioned SDN or an opaque encoding of that contract, with
a query digest and continuation position/frontier token. The digest includes
snapshot, generation, operation, roots, relation/direction/filter/precision,
depth, page size, visibility policy and deterministic order version. Validate
before allocation or lookup. Cross-user remote adapters derive visibility
context from their trusted caller boundary; the client cannot self-assert it.
An in-process record is not a security capability merely because it is typed.

Paged node views may include induced edges, but label that limitation. Full
graph export pages node records and edge records independently with stable
IDs and validates all endpoints after reconstruction; never lose cross-page
edges. Qualification operates on the admitted graph/evidence scope, not on a
rendered slice. Hidden counts may themselves need redaction.

Schema migration dispatches explicitly by version. Keep v1 graph/declaration
readers, version new nodes/relations and reject unsupported writers. Import
legacy grouping with source path/digest, old/new identity and explicit mapping
provenance; ambiguous identity is a diagnostic. `contains` cycle checks cover
cross-file and nested groups, independent of manifest placement.

## Report, code matrix and adapter behavior

CLI proposed commands are listed in the [TUI sketch](extreme_typing_traceability_tui.md).
Table is human default; `--format=sdn` is the structured contract. JSON is an
explicit interoperability adapter, never an internal replacement store.
Markdown/HTML use the same projection and explicit `--output` destination.
Sort by stable identity, omit volatile generation timestamps from structural
content, and put freshness/provenance in a separately identified run context.
Use atomic destination writes, safe relative source links and no script/remote
resource execution. Sanitize before serialization and rendering; validate
file URL/path schemes, traversal, symlinks and output collisions.

Feature/layer cells hold sets of semantic symbols and membership provenance.
Dependency cells hold sets of directed code relation identities plus precision
counts. Shared symbols count once in each set; totals use union. Preserve
unknown membership and unresolved call counts. Neither a zero visible cell nor
an omitted private cell proves no dependency.

LSP/MCP adapters expose bounded queries, cancellation and explicit stale/resync
responses. Reuse immutable index generations and caller authorization. The
editor's unsaved buffer can be a separately captured snapshot, never silently
joined to staged/Git facts. Slop handles layout/focus only. Caret compares
registered snapshot sets without spawning Git per pane refresh. PR refresh is
an explicit effect with cached freshness; offline unavailability is visible.

## Query authorization and cache freshness clarification

Cursor binding includes effective caller identity, allowed scope and
authorization epoch, not just a shared policy name/version. Authorization
filters root lookup, traversal intermediates, returned edges, counts, frontiers
and diagnostics before projection. A bounded path search with an unexplored
frontier returns incomplete/unknown instead of "no path".

Compiler verdict caches bind deterministic semantic/source/policy/type/target
inputs and invalidate on changes; no arbitrary wall-clock expiry is required.
External admission/evidence and PR metadata have separate trust/freshness
policies. Native graph interfaces remain SDN; any JSON facility is a separately
requested external interoperability adapter.

## Errors and qualification

Stable categories: invalid query/cursor, missing entity, incomplete capture,
stale generation, unresolved semantic type, forbidden export, unsupported
schema, budget exhausted, unauthorized material and unavailable provider.
Keep diagnostics bound to subject/rule/entity/provenance, and preserve the
last valid display without presenting it as current green.

Evidence admission remains separate from pure eligibility. Current
`evidence.spl` compares a supplied trusted context but does not independently
certify producer or artifact bytes. A `PublicApiSurface` fact or API violation
record is source evidence, not proof of an executed check. Proof obligations
must bind actual production IR/transform versions and durable reviewed proof
artifacts; unsupported properties remain blocked. See the test and phase plans
for deliberate-red, engine-parity and qualification gates.
